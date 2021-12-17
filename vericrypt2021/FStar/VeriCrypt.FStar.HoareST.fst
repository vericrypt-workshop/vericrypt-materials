module VeriCrypt.FStar.HoareST

/// Deriving a hoare logic for stateful programs,
///   and integrating it into F* as a shallow-embedding
///
/// I.e. at the end of it, we would like to write F* programs
///   that are typechecked according to the logic rules that we define
///
/// This is quite powerful: you can define your own program logic,
///   and program with it in the dependent type theory of F*,
///   with refinements, recursive functions, inductives etc. given to you for free!

/// The types of pre- and postconditions for our hoare logic for stateful programs
///
/// Note that we fix the type of the state to Type0,
///   usually the type of the state is one universe higher than the values it stores

type req_t (s:Type0) = s -> Type0
type ens_t (s:Type0) (a:Type) = s -> a -> s -> Type0


/// Type of a stateful computation
///
/// Under the hood, it is a pure function that manipulates the state

type repr (a:Type) (s:Type0) (req:req_t s) (ens:ens_t s a) =
  s0:s -> Pure (a & s) (requires req s0) (ensures fun (r, s1) -> ens s0 r s1)

/// Let's now define basic combinators
///
/// First, a return to tell F* how to inject values into stateful computations
///
/// Think of it as the Hoare logic rule for values

unfold
let return_pre (s:Type0) : req_t s = fun _ -> True

unfold
let return_post (#a:Type) (s:Type0) (x:a) : ens_t s a =
  fun s0 r s1 -> s0 == s1 /\ r == x

let return (a:Type) (x:a) (s:Type0)
  : repr a s (return_pre s) (return_post s x)
  = fun s0 -> x, s0

/// Next is bind, the Hoare logic rule for sequential composition
///   of two stateful computations

unfold
let bind_pre (#a:Type) (#s:Type0)
  (req_f:req_t s) (ens_f:ens_t s a)
  (req_g:a -> req_t s)
  : req_t s
  = fun s0 -> req_f s0 /\ (forall (x:a) (s1:s). ens_f s0 x s1 ==> req_g x s1)

unfold
let bind_post (#a #b:Type) (#s:Type0)
  (ens_f:ens_t s a) (ens_g:a -> ens_t s b)
  : ens_t s b
  = fun s0 y s2 -> exists (x:a) (s1:s). ens_f s0 x s1 /\ ens_g x s1 y s2

let bind (a b:Type) (s:Type0)
  (req_f:req_t s) (ens_f:ens_t s a)
  (req_g:a -> req_t s) (ens_g:a -> ens_t s b)
  (f:repr a s req_f ens_f) (g:(x:a -> repr b s (req_g x) (ens_g x)))
  : repr b s (bind_pre req_f ens_f req_g)
             (bind_post ens_f ens_g)
  = fun s0 ->
    let x, s1 = f s0 in
    g x s1

/// Subcomp combinator defines subtyping between the computation types
///   of the new effect

unfold
let subcomp_pre (#a:Type) (#s:Type0)
  (req_f:req_t s) (ens_f:ens_t s a)
  (req_g:req_t s) (ens_g:ens_t s a)
  : pure_pre
  = (forall s0. req_g s0 ==> req_f s0) /\
    (forall s0 x s1. ens_f s0 x s1 ==> ens_g s0 x s1)

let subcomp (a:Type) (s:Type0)
  (req_f:req_t s) (ens_f:ens_t s a)
  (req_g:req_t s) (ens_g:ens_t s a)
  (f:repr a s req_f ens_f)
  : Pure (repr a s req_g ens_g)
         (requires subcomp_pre req_f ens_f req_g ens_g)
         (ensures fun _ -> True)
  = f

/// Now package it up as a new F* effect

/// The reflectable annotation says that we may `reflect` computations
///   from their `repr` type to `MST` effect
///
/// Think of `reflect` as a coercion from `repr` to `MST`,
///   see `get_s` and `put_s` below

reflectable
effect {
  MST (a:Type) (s:Type0) (req:req_t s) (ens:ens_t s a)
  with {repr; return; bind; subcomp}
}

/// We also define a lift from PURE to MST

/// The following two combinators define how to interpret a pure wp
///   as a stateful requires and ensures

unfold
let lift_pure_st_req (#a:Type) (s:Type0) (wp:pure_wp a) : req_t s =
  fun _ -> as_requires wp /\ True

unfold
let lift_pure_st_ens (#a:Type) (s:Type0) (wp:pure_wp a) : ens_t s a =
  fun s0 r s1 -> s0 == s1 /\ as_ensures wp r

let lift_PURE_MST (a:Type) (s:Type0)
  (wp:pure_wp a)
  (f:eqtype_as_type unit -> PURE a wp)
  : repr a s (lift_pure_st_req s wp) (lift_pure_st_ens s wp)
  = fun s0 ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let x = f () in
    x, s0

/// Request F* to use lift_PURE_MST to lift PURE computations to MST

sub_effect PURE ~> MST = lift_PURE_MST

/// Let's also define two actions, `get` and `put` that manipulate state

let get_s (s:Type0) : MST s s (fun _ -> True) (fun s0 r s1 -> s0 == r /\ r == s1) =
  MST?.reflect (fun s0 -> s0, s0)

let put_s (#s:Type0) (x:s) : MST unit s (fun _ -> True) (fun _ _ s1 -> s1 == x) =
  MST?.reflect (fun _ -> (), x)


/// We now have an MST effect, that implements our program logic,
///   in our hands that we can write programs with!

/// Let's customize MST to int state

effect MSTInt (a:Type) (req:req_t int) (ens:ens_t int a) = MST a int req ens

/// And the `get` and `put` functions as well

let get () : MSTInt int (fun _ -> True) (fun s0 r s1 -> s0 == r /\ r == s1) = get_s int

let put (n:int) : MSTInt unit (fun _ -> True) (fun _ _ s1 -> s1 == n) = put_s n

/// A function to increment the state
///
/// Note what's happening here:
///
/// F* typechecks the function body, invoking the rules for ST bind,
///   lifting PURE computations (e.g. n+1) using the lift,
///   and computes a spec
///
///   Then it applies subcomp to check that the inferred spec is subsumed
///   by the annotated spec

let incr_st (m:int) : MSTInt unit (fun _ -> True) (fun s0 _ s1 -> s1 == s0 + m) =
  let n = get () in
  put (n+m)

/// We can seamlessly use inductives, recursion, refinements, etc.
///   with our new effect
///
/// For example, we can go through a list of nat, and add all the elements to the state
///
/// The returns annotation provides dependent pattern matching
///   Without this, we would a way to combine the two branches
///   That's also possible using an if-then-else effect combinator

let rec incr_list (l:list nat)
  : MSTInt unit (fun _ -> True) (fun s0 _ s1 -> s1 >= s0)
  = match l returns MSTInt unit (fun _ -> True) (fun s0 _ s1 -> s1 >= s0) with
    | [] -> ()
    | hd::tl ->
      let n = get () in
      put (n+hd);
      incr_list l


/// Hmm, termination?

/// We can mark the effect total if we want
