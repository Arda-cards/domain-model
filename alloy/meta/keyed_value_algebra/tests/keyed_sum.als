module meta/keyed_value_algebra/tests/keyed_sum
// Reflects dafny-domain src/meta/tests/scalar-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/keyed_value_algebra/keyed_monoid
open meta/keyed_value_algebra/keyed_sum[N]     // Fold (over N), chainSum, rangeSum, headSum, lastSum

// Σ-along-an-order over the keyed monoid, on a test carrier `N`. Test keys `K` are uninterpreted.
// `exactly 3 Scalar` + `ringAxioms` pins the abstract ring to ℤ/3 (a PREMISE). Scope `5` ⇒ chains ≤ ~5.
sig N {}                                       // test carrier (the fold nodes)
sig K {}
fact KeysOnly { all n: N | Fold.val[n] in K -> lone Scalar }   // keep the keyspace to K in tests

// --- a multi-node fold chain exists (SAT) ---
run unit_sum_loads {
  ringAxioms and (some n: N | some Fold.earlier[n] and some Fold.earlier[Fold.earlier[n]])
} for 5 but exactly 3 Scalar expect 1

// --- the running total WIDENS along the chain: two single-key, different-key nodes → a 2-key total ---
run unit_sum_widensAlongChain {
  ringAxioms and
  (some n1, n2: N |
     no Fold.earlier[n1] and Fold.earlier[n2] = n1 and
     isSingle[Fold.val[n1]] and isSingle[Fold.val[n2]] and
     Fold.val[n1].Scalar != Fold.val[n2].Scalar and    // different KEY sets
     isMulti[Fold.cum[n2]])                             // ⇒ the cumulative carries both keys
} for 5 but exactly 3 Scalar expect 1

// --- base: at the head the running total is just that node's value ---
check unit_sum_baseIsVal {
  all n: N | no Fold.earlier[n] implies Fold.cum[n] = Fold.val[n]
} for 5 but exactly 3 Scalar expect 0

// --- step: each later total folds the previous total with this node's value ---
check unit_sum_stepFolds {
  all n: N | some Fold.earlier[n] implies Fold.cum[n] = add[Fold.cum[Fold.earlier[n]], Fold.val[n]]
} for 5 but exactly 3 Scalar expect 0

// --- the cumulative stays in normal form all the way down the chain ---
check unit_sum_cumNf {
  all n: N | nf[Fold.cum[n]]
} for 5 but exactly 3 Scalar expect 0

// --- telescoping is sound: prefix total ⊕ (sub-chain from m to the end) = the whole-chain total ---
check unit_sum_telescope {
  ringAxioms implies
    all m: N | some Fold.earlier[m] implies
      add[Fold.cum[Fold.earlier[m]], rangeSum[m, lastSum[m]]] = chainSum[m]
} for 5 but exactly 3 Scalar expect 0
