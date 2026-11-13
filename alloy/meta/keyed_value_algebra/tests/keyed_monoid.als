module meta/keyed_value_algebra/tests/keyed_monoid
// Reflects dafny-domain src/meta/tests/scalar-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/keyed_value_algebra/keyed_monoid

// Uninterpreted test keys — the algebra holds for an arbitrary key type. `exactly 3
// Scalar` + `ringAxioms` pins the abstract ring to a 3-element commutative ring (ℤ/3).
// `ringAxioms` is the PREMISE (it is not a global fact), so every command assumes it.

sig K {}

// --- a valid scalar ring exists ---
run unit_alg_loads { ringAxioms } for 3 but exactly 3 Scalar expect 1

// --- demonstrations of the behaviour (existential, under the ring) ---
run unit_alg_widen {
  ringAxioms and
  (some a, b: K -> lone Scalar |
    isSingle[a] and isSingle[b] and a.Scalar != b.Scalar and isMulti[add[a, b]])
} for 3 but exactly 3 Scalar expect 1
run unit_alg_collapse {
  ringAxioms and (some a: K -> lone Scalar | isSingle[a] and isZero[add[a, negate[a]]])
} for 3 but exactly 3 Scalar expect 1
run unit_alg_scaleZero {
  ringAxioms and (some a: K -> lone Scalar | isSingle[a] and isZero[scale[SZero, a]])
} for 3 but exactly 3 Scalar expect 1
run unit_alg_scaleOne {
  ringAxioms and (some a: K -> lone Scalar | isSingle[a] and scale[SOne, a] = a)
} for 3 but exactly 3 Scalar expect 1

// --- keyed-algebra laws (assume the ring; small scope) ---
check unit_alg_addCommutative {
  ringAxioms implies all a, b: K -> lone Scalar | (nf[a] and nf[b]) implies add[a, b] = add[b, a]
} for 3 but exactly 3 Scalar expect 0

check unit_alg_addIdentity {
  ringAxioms implies all a: K -> lone Scalar | nf[a] implies add[a, zero] = a
} for 3 but exactly 3 Scalar expect 0

check unit_alg_addClosedNf {
  ringAxioms implies all a, b: K -> lone Scalar | (nf[a] and nf[b]) implies nf[add[a, b]]
} for 3 but exactly 3 Scalar expect 0

check unit_alg_addAssociative {
  ringAxioms implies all a, b, c: K -> lone Scalar |
    (nf[a] and nf[b] and nf[c]) implies add[add[a, b], c] = add[a, add[b, c]]
} for 3 but exactly 3 Scalar expect 0

check unit_alg_addInverse {
  ringAxioms implies all a: K -> lone Scalar | nf[a] implies add[a, negate[a]] = zero
} for 3 but exactly 3 Scalar expect 0

check unit_alg_scaleZeroScalar {
  ringAxioms implies all a: K -> lone Scalar | scale[SZero, a] = zero
} for 3 but exactly 3 Scalar expect 0
check unit_alg_scaleZeroValue {
  ringAxioms implies all s: Scalar | scale[s, zero] = zero
} for 3 but exactly 3 Scalar expect 0
check unit_alg_scaleOneIdentity {
  ringAxioms implies all a: K -> lone Scalar | nf[a] implies scale[SOne, a] = a
} for 3 but exactly 3 Scalar expect 0
check unit_alg_scaleDistribAdd {
  ringAxioms implies all s: Scalar, a, b: K -> lone Scalar |
    (nf[a] and nf[b]) implies scale[s, add[a, b]] = add[scale[s, a], scale[s, b]]
} for 3 but exactly 3 Scalar expect 0
