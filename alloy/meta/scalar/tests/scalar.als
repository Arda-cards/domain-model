module meta/scalar/tests/scalar
// Reflects dafny-domain src/meta/tests/scalar-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/scalar/scalar

// The abstract Scalar ring. `ringAxioms` is a PREMISE (assumed per command); `exactly 3 Scalar` pins a
// concrete witness (ℤ/3). A concrete bounded fixed-point model is verified in
// meta/keyed_value_algebra/tests/scalar_int.

// A non-trivial commutative ring with unit exists at this carrier size.
run unit_scalar_ringExists { ringAxioms } for exactly 3 Scalar expect 1

// The ring is non-trivial (0 ≠ 1) — follows from ringAxioms.
check unit_scalar_zeroNeOne { ringAxioms implies SZero != SOne } for 3 Scalar expect 0

// Every element has an additive inverse.
check unit_scalar_addInverse {
  ringAxioms implies all a: Scalar | a.splus[a.sneg] = SZero
} for exactly 3 Scalar expect 0

// Multiplication distributes over addition.
check unit_scalar_distributes {
  ringAxioms implies all a, b, c: Scalar | a.smul[b.splus[c]] = (a.smul[b]).splus[a.smul[c]]
} for exactly 3 Scalar expect 0
