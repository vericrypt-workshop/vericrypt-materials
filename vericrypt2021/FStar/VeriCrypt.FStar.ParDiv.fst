module VeriCrypt.FStar.ParDiv

module U = FStar.Universe

(*
 * Nikhil Swamy wrote this version of the semantics,
 *   based on this Aseem Rastogi wrote the full semantics of Steel (see ulib/experimental/Steel.Semantics.Hoare.MST.fst)
 *)

/// In VeriCrypt.FStar.HoareST, we derived a Hoare logic for stateful programs
///   using state passing functions as the underlying representation of stateful
///   functions
///
/// But how do we derive program logics for other domains such as concurrency,
///   given that F* does not have any primitive support for it
///
/// In this module, we provide a semantic model for concurrency, state, and divergence,
///   and also derive a Concurrent Separation Logic (CSL) for the semantics
///
/// The basic idea is to represent a concurrent computation as an action tree,
///   and provide a definitional interpreter for it that implements an
///   interleaving semantics
///
/// Then we package is up as an effect (similar to what we did for HoareST),
///   but this time using the action tree as the underlying representation
///
/// One interesting aspect of the development is that the definitional interpreter
///   intrinsically derives a program logic too


/// We start by defining some basic notions for a commutative monoid
///
/// (Separating conjunction in CSL satisfies these properties.)

let associative #a (f: a -> a -> a) =
  forall x y z. f x (f y z) == f (f x y) z

let commutative #a (f: a -> a -> a) =
  forall x y. f x y == f y x

let is_unit #a (x:a) (f:a -> a -> a) =
  forall y. f x y == y /\ f y x == y  //x is a unit for f


/// In addition to being a commutative monoid over the carrier [r]
///   a [comm_monoid s] also gives an interpretation of `r` as a predicate on states [s]

noeq
type comm_monoid (s:Type) = {
  r:Type;
  emp: r;
  star: r -> r -> r;
  interp: r -> s -> prop;
  laws: squash (associative star /\ commutative star /\ is_unit emp star)
}


/// [post a c] is a postcondition on [a]-typed result

let post #s a (c:comm_monoid s) = a -> c.r


/// [action c s]: atomic actions are, intuitively, single steps of
/// computations interpreted as a [s -> a & s]
/// 
/// However, we augment them with two features:
///   1. they have pre-condition [pre] and post-condition [post]
///   2. their type guarantees that they are frameable
///
/// (Matt Parkinson suggested this style of setting up actions.)

noeq
type action #s (c:comm_monoid s) (a:Type) = {
   pre: c.r;
   post: a -> c.r;
   sem: (frame:c.r ->
         s0:s{c.interp (c.star pre frame) s0} ->
         (x:a & s1:s{c.interp (post x `c.star` frame) s1}));
}


/// [m s c a pre post] :
///
///   A free monad for divergence, state and parallel composition
///   with generic actions. The main idea:
///
///   Every continuation may be divergent. As such, [m] is indexed by
///   pre- and post-conditions so that we can do proofs intrinsically
///
/// Universe-polymorphic in both the state and result type

noeq
type m (#s:Type u#s) (#c:comm_monoid u#s u#s s) : (a:Type u#a) -> c.r -> post a c -> Type =
  | Ret : #a:_ -> #post:(a -> c.r) -> x:a -> m a (post x) post
  | Act : #a:_ -> #post:(a -> c.r) -> #b:_ -> f:action c b -> k:(x:b -> Dv (m a (f.post x) post)) -> m a f.pre post
  | Par : pre0:_ -> post0:_ -> m0: m (U.raise_t unit) pre0 (fun _ -> post0) ->
          pre1:_ -> post1:_ -> m1: m (U.raise_t unit) pre1 (fun _ -> post1) ->
          #a:_ -> #post:_ -> k:m a (c.star post0 post1) post ->
          m a (c.star pre0 pre1) post

/// We assume a stream of booleans as a parameter to the semantics
///   to resolve the nondeterminism of Par

assume val bools : nat -> bool


/// The semantics comes is in two levels:
///
///   1. A single-step relation [step] which selects an atomic action to
///      execute in the tree of threads
///
///   2. A top-level driver [run] which repeatedly invokes [step]
///      until it returns with a result and final state.

/// [step_result s c a q frame]:
///
///   The result of evaluating a single step of a program
///     - s, c: The state and its monoid
///     - a : the result type
///     - q : the postcondition to be satisfied after fully reducing the programs
///     - frame: a framed assertion to carry through the proof

noeq
type step_result s (c:comm_monoid s) a (q:post a c) (frame:c.r) =
  | Step: p:_ -> //precondition of the reduct
          m a p q -> //the reduct
          state:s {c.interp (p `c.star` frame) state} -> //the next state, satisfying the precondition of the reduct
          nat -> //position in the stream of booleans (less important)
          step_result s c a q frame

/// [step i f frame state]: Reduces a single step of [f], while framing
///   the assertion [frame]

let rec step #s #c (i:nat) #pre #a #post (f:m a pre post) (frame:c.r) (state:s)
  : Div (step_result s c a post frame)
        (requires
          c.interp (pre `c.star` frame) state)
        (ensures fun _ -> True)
  = match f with
    | Ret x ->
      //The computation is already terminal, just return
      Step (post x) (Ret x) state i

    | Act act1 k ->
      //Evaluate the action and return the continuation as the reduct
      let (| b, state' |) = act1.sem frame state in
      Step (act1.post b) (k b) state' i

    | Par pre0 post0 (Ret x0)
          pre1 post1 (Ret x1)
          k ->
      //If both sides of a `Par` have returned
      //then step to the continuation
      Step (post0 `c.star` post1) k state i

    | Par pre0 post0 m0
          pre1 post1 m1
          k ->
      //Otherwise, sample a boolean and choose to go left or right to pick
      //the next command to reduce
      //The two sides are symmetric
      if bools i
      then let Step pre0' m0' state' j =
             //Notice that, inductively, we instantiate the frame extending
             //it to include the precondition of the other side of the par
             step (i + 1) m0 (pre1 `c.star` frame) state in
           Step (pre0' `c.star` pre1) (Par pre0' post0 m0' pre1 post1 m1 k) state' j
      else let Step pre1' m1' state' j =
             step (i + 1) m1 (pre0 `c.star` frame) state in
           Step (pre0 `c.star` pre1') (Par pre0 post0 m0 pre1' post1 m1' k) state' j

/// [run i f state]: Top-level driver that repeatedly invokes [step]
///
/// The type of [run] is the main theorem. It states that it is sound
///   to interpret the indices of `m` as a Hoare triple in a
///   partial-correctness semantics

let rec run #s #c (i:nat) #pre #a #post (f:m a pre post) (state:s)
  : Div (a & s)
    (requires
      c.interp pre state)
    (ensures fun (x, state') ->
      c.interp (post x) state')
  = match f with
    | Ret x -> x, state
    | _ ->
      let Step pre' f' state' j = step i f c.emp state in
      run j f' state'

/// We will now package the tree as an effect


/// [return] combinator
let return #s (#c:comm_monoid s) #a (x:a) (post:a -> c.r)
  : m a (post x) post
  = Ret x

/// [bind]: sequential composition works by pushing `g` into the continuation
///   at each node, finally applying it at the terminal `Ret`

let rec bind (#s:Type u#s)
             (#c:comm_monoid s)
             (#a:Type u#a)
             (#b:Type u#b)
             (#p:c.r)
             (#q:a -> c.r)
             (#r:b -> c.r)
             (f:m a p q)
             (g: (x:a -> Dv (m b (q x) r)))
  : Dv (m b p r)
  = match f with
    | Ret x -> g x  //if f is terminal, apply the value x to g
    | Act act k ->
      Act act (fun x -> bind (k x) g)  //push g into the action continuation
                                    //essentially, first the action will execute,
                                    //then its continuation, and then g
    | Par pre0 post0 ml
          pre1 post1 mr
          k ->
      let k : m b (post0 `c.star` post1) r = bind k g in
      let ml' : m (U.raise_t u#0 u#b unit) pre0 (fun _ -> post0) =
         bind ml (fun _ -> Ret (U.raise_val u#0 u#b ()))
      in
      let mr' : m (U.raise_t u#0 u#b unit) pre1 (fun _ -> post1) =
         bind mr (fun _ -> Ret (U.raise_val u#0 u#b ()))
      in
      Par #s #c pre0 post0 ml'
                pre1 post1 mr'
                #b #r k

(* Next, a main property of this semantics is that it supports the
   frame rule. Here's a proof of it *)

/// First, we prove that individual actions can be framed
///
/// --- That's not so hard, since we specifically required actions to
///     be frameable

let frame_action (#s:Type) (#c:comm_monoid s) (#a:Type) (f:action c a) (fr:c.r)
  : g:action c a { g.post == (fun x -> f.post x `c.star` fr) /\
                   g.pre == f.pre `c.star` fr }
  = let pre = f.pre `c.star` fr in
    let post x = f.post x `c.star` fr in
    let sem (frame:c.r) (s0:s{c.interp (c.star pre frame) s0})
      : (x:a & s1:s{c.interp (post x `c.star` frame) s1})
      = let (| x, s1 |) = f.sem (fr `c.star` frame) s0 in
        (| x, s1 |)
    in
    { pre = pre;
      post = post;
      sem = sem }

/// Now, to prove that computations can be framed, we'll just thread
/// the frame through the entire computation, passing it over every
/// frameable action

let rec frame (#s:Type u#s)
              (#c:comm_monoid s)
              (#a:Type u#a)
              (#p:c.r)
              (#q:a -> c.r)
              (fr:c.r)
              (f:m a p q)
   : Dv (m a (p `c.star` fr) (fun x -> q x `c.star` fr))
   = match f with
     | Ret x -> Ret x
     | Act f k ->
       Act (frame_action f fr) (fun x -> frame fr (k x))
     | Par pre0 post0 m0 pre1 post1 m1 k ->
       Par (pre0 `c.star` fr) (post0 `c.star` fr) (frame fr m0)
           pre1 post1 m1
           (frame fr k)

/// [par]: Parallel composition
///   Works by just using the `Par` node and `Ret` as its continuation

let par #s (#c:comm_monoid s)
        #p0 #q0 (m0:m unit p0 (fun _ -> q0))
        #p1 #q1 (m1:m unit p1 (fun _ -> q1))
 : Dv (m unit (p0 `c.star` p1) (fun _ -> q0 `c.star` q1))
 = let m0' : m (U.raise_t unit) p0 (fun _ -> q0) =
       bind m0 (fun _ -> Ret (U.raise_val u#0 u#0 ()))
   in
   let m1' : m (U.raise_t unit) p1 (fun _ -> q1) =
     bind m1 (fun _ -> Ret (U.raise_val u#0 u#0 ()))
   in
   Par p0 q0 m0'
       p1 q1 m1'
       (Ret ())

/// Assume some heap and an associated monoid for assertions

/// Now for an instantiation of the state with a heap
/// just to demonstrate how that would go

/// Heaps are usually in a universe higher than the values they store
/// Pick it in universe 1
assume val heap : Type u#1
[@@erasable]
assume type r : Type u#1
assume val emp : r
assume val star : r -> r -> r
assume val interp : r -> heap -> prop
/// Assume some monoid of heap assertions
let hm : comm_monoid u#1 u#1 heap = {
  r = r;
  emp = emp;
  star = star;
  interp = interp;
  laws = magic()
}


/// The representation of our effect is a thunked, potentially divergent `m` computation

let comp (a:Type u#a) (p:hm.r) (q:a -> hm.r)
  = unit -> Dv (m a p q)

let ret (a:Type u#a) (x:a) (p: a -> hm.r)
  : comp a (p x) p
  = fun _ -> return x p

let bnd (a:Type u#a) (b:Type u#b) (p:hm.r) (q: a -> hm.r) (r: b -> hm.r)
        (f:comp a p q) (g: (x:a -> comp b (q x) r))
  : comp b p r
  = fun _ -> bind (f()) (fun x -> g x ())

reifiable
reflectable
effect {
   C (a:Type) (pre:hm.r) (q: a -> hm.r)
   with { repr = comp;
          return = ret;
          bind = bnd }
}
