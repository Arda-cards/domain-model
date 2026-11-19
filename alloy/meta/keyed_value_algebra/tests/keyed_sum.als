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
