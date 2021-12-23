module VeriCrypt.FStar.Basics

open FStar.Mul

/// F* standard libraries (see e.g. ulib/prims.fst) define some basic types
///   such as unit, bool, int, option, tuple, list, etc.
///
/// Note that the nat type used here is a refinement type defined in prims

let incr (n:nat) : nat = n + 1

let rec sum (n:nat) : nat =
  if n = 0 then 0
  else n + sum (n-1)

/// We can prove some properties about the sum function
///
/// The following is a proof-by-induction,
///   where n = 0 is the base case,
///   and the recursive lemma call applies the induction hypothesis,
///   Z3 is able to fill-in rest of the proof

let rec sum_geq_n (n:nat)
  : Lemma (sum n >= n)
  = if n = 0 then ()
    else sum_geq_n (n-1)

/// Fill-in this proof
///
/// The `requires` precondition is available in the lemma body
///
/// F* will typecheck that the callers of the lemma have to satisfy the precondition

let rec sum_monotonic (m n:nat)
  : Lemma (requires m >= n)
          (ensures sum m >= sum n)
  = admit ()

/// In a similar vein, we can also define factorial
///   and prove properties about it

let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n-1)

/// Fill-in this proof

let rec factorial_geq_n (n:nat)
  : Lemma (factorial n >= n)
  = admit ()

/// See the list inductive type in prims.fst,
///   and some functions on lists in FStar.List.Tot.Base.fst, FStar.List.Tot.Properties.fst
///
/// Reproducing some of it below

let rec length (#a:Type) (l:list a) : nat =
  match l with
  | [] -> 0
  | _::tl -> 1 + length tl

/// E.g. append [1; 2] [2; 3] = [1; 2; 2; 3]

let rec append (#a:Type) (l1 l2:list a) : list a =
  match l1 with
  | [] -> l2
  | hd::tl -> hd::(append tl l2)

/// We can prove properties about length and append
///
/// Fill-in the proof

let rec length_append (#a:Type) (l1 l2:list a)
  : Lemma (length (append l1 l2) == length l1 + length l2)
  = admit ()

/// We can also write higher-order functions,
///   like map that maps a function over a list

let rec map (#a #b:Type) (f:a -> b) (l:list a) : list b =
  match l with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

/// Map incr over a list

let t0 = assert (map incr [1; 2] == [2; 3])

/// The proof above relies on Z3 to do the computation
///
/// To avoid Z3 unfolding recursive definitions indefinitely,
///   we allow only unlimited unrolling
///
/// Therefore the following example fails, since the number of unrollings
///   needed is higher than the default limit

[@@ expect_failure]
let t1 = assert (map incr [1; 2; 3; 4; 5; 6; 7; 8] ==
                          [2; 3; 4; 5; 6; 7; 8; 9])

/// We can use other F* features to do the proof,
///   e.g. we can let F* compute it, rather than relying on Z3

let t1 = assert_norm (map incr [1; 2; 3; 4; 5; 6; 7; 8] ==
                               [2; 3; 4; 5; 6; 7; 8; 9])

/// We can also use tactics to the proof, see our ESOP'19 paper on fstar-lang.org


/// We now define an inductive type family for length-indexed vectors
///
/// The vector type is indexed with its length

type vector (a:Type) : nat -> Type =
  | VNil  : vector a 0
  | VCons : #n:nat -> hd:a -> tl:vector a n -> vector a (n+1)


/// Fill-in the vappend function

let rec vappend (#a:Type) (#n1 #n2:nat) (v1:vector a n1) (v2:vector a n2)
  : vector a (n1+n2)
  = admit ()

/// Note we don't need a lemma for length of vappend, it's there in the index!

/// Exercise:
///
/// Write a map function for vectors, call it vmap, and prove a lemma that
///   vmap commutes with vappend, i.e. roughly
///   (vmap (vappend v1 v2) == vappend (vmap v1) (vmap v2))

/// Exercise:
///
/// Define a function to reverse a vector, call it rev, and prove that
///   rev is involutive, i.e. rev (rev v) == v


/// Semantics termination checking:
///
/// In the examples so far, proving that the recursive functions terminate
///   is straightforward, F* is itself able to figure out the termination metric
///
/// But what about the following (a bit contrived) example:

/// Assume there is a function f from nat to nat

assume val f : nat -> nat

/// Then, there is a function g that given a nat, returns a nat s.t.:

assume val g : n:nat -> m:nat{f m < f n}

/// Let's try to write a recursive function,
///   that recursively invokes itself on the return value of g

[@@ expect_failure]
let rec test_decreases (n:nat) : nat =
  test_decreases (g n)

/// F* allows any pure function to be specified as termination metric
///
/// `Tot` is an effect label for total functions
///
/// When the effect label is missing, it defaults to Tot

let rec test_decreases (n:nat) : Tot nat (decreases (f n)) =
  test_decreases (g n)
