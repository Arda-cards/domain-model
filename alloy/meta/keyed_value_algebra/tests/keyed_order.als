module meta/keyed_value_algebra/tests/keyed_order
// Reflects dafny-domain src/meta/tests/scalar-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/keyed_value_algebra/keyed_order

// Uninterpreted test keys. Every command assumes BOTH premises (the scalar ring AND the
// posited order); `exactly 3 Scalar` pins a small concrete carrier (ℤ/3 with a linear order).
sig K {}
pred premises { ringAxioms and orderAxioms }

run unit_ord_loads { premises } for 3 but exactly 3 Scalar expect 1

// --- demonstrations (the interesting cases EXIST; SAT) ---
run unit_ord_indeterminateSign {
  premises and (some a: K -> lone Scalar | classify[a] = INDETERMINATE)
} for 3 but exactly 3 Scalar expect 1
run unit_ord_undeterminedEquality {
  premises and (some a, b: K -> lone Scalar | semanticEq[a, b] = UNDETERMINED)
} for 3 but exactly 3 Scalar expect 1
run unit_ord_incomparable {
  premises and (some a, b: K -> lone Scalar | nf[a] and nf[b] and not lte[a, b] and not lte[b, a])
} for 3 but exactly 3 Scalar expect 1
