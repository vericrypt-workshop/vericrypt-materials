module VeriCrypt.FStar.PureDiv

/// Behind the scenes, F* provides a "primitive" PURE effect
///   indexed with monadic specifications in the form of
///   weakest precondition transformers
///
/// In this module, we will use a Hoare-style abbreviation of PURE, called Pure,
///   with pre- and postconditions
///
/// See prims.fst for how this abbreviation is defined

let incr (n:nat) : Pure nat (requires True) (ensures fun r -> r == n+1) = n + 1


/// We can also give a weaker specification to incr
///
/// Though it doesn't matter too much in this small example,
///   in large developments, judicious weakening of specs may provide better automation mileage

let incr2 (n:nat) : Pure nat (requires True) (ensures fun r -> r >= n) = n + 1

/// Exercise:
///
/// Take the factorial function from VeriCrypt.FStar.Basics,
///   and try giving it different specs using Pure


/// `Lemma req ens` is sugar for `Pure unit req (fun _ -> ens)`
///
/// Even `Tot a` is a sugar (`Pure a (requires True) (ensures fun _ -> True)`)


/// F* has coercive subtyping with seamless interaction between
///   refinements and specifications
///
/// Notice how F* is able to typecheck the call to `incr` that expects a `nat`,
///   based on the precondition of `test_incr`

let test_incr (n:int) : Pure int (requires n >= 0) (ensures fun _ -> True) =
  incr n


/// F* also has a primitive effect for divergent programs, called DIV
///
/// DIV functions may not terminate

/// The sum function below terminates only for n >= 0
///
/// Removing Dv, and hence asking F* to typecheck it as a total function, would fail

let rec sum (n:int) : Dv int =
  if n = 0 then 1
  else n + sum (n-1)


/// For such functions, we can prove their properties only intrinsically,
///   i.e. as part of specs, not as separate lemmas

let rec sum_geq_n (n:int) : Div int (requires True) (ensures fun r -> n >= 0 ==> r >= n) =
  if n = 0 then 1
  else n + sum_geq_n (n - 1)


/// Exercise: Try proving a lemma about a Div function, e.g. sum above
///
/// What error do you get and why?
