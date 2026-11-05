module meta/keyed_value_algebra/tests/keyed_order
// Reflects dafny-domain src/meta/tests/scalar-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/keyed_value_algebra/keyed_order

// Uninterpreted test keys. Every command assumes BOTH premises (the scalar ring AND the
// posited order); `exactly 3 Scalar` pins a small concrete carrier (ℤ/3 with a linear order).
sig K {}
pred premises { ringAxioms and orderAxioms }

run unit_ord_loads { premises } for 3 but exactly 3 Scalar expect 1

// --- the product order is a partial order (these DO hold; UNSAT = no counterexample) ---
check unit_ord_lteReflexive {
  premises implies all a: K -> lone Scalar | lte[a, a]
} for 3 but exactly 3 Scalar expect 0
check unit_ord_lteTransitive {
  premises implies all a, b, c: K -> lone Scalar | (lte[a, b] and lte[b, c]) implies lte[a, c]
} for 3 but exactly 3 Scalar expect 0
check unit_ord_lteAntisymmetric {
  premises implies all a, b: K -> lone Scalar | (nf[a] and nf[b] and lte[a, b] and lte[b, a]) implies a = b
} for 3 but exactly 3 Scalar expect 0

// --- sign classification agrees with the order against ZERO ---
check unit_ord_positiveIsAboveZero {
  premises implies all a: K -> lone Scalar |
    nf[a] implies (classify[a] = POSITIVE iff (not isZero[a] and lte[zero, a]))
} for 3 but exactly 3 Scalar expect 0

// --- semantic equality: EQUAL exactly when lexically equal; UNEQUAL ⇒ really different ---
check unit_ord_semEqualIffLexical {
  premises implies all a, b: K -> lone Scalar |
    (nf[a] and nf[b]) implies (semanticEq[a, b] = EQUAL iff lexEq[a, b])
} for 3 but exactly 3 Scalar expect 0
check unit_ord_semUnequalImpliesDifferent {
  premises implies all a, b: K -> lone Scalar | semanticEq[a, b] = UNEQUAL implies a != b
} for 3 but exactly 3 Scalar expect 0

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
