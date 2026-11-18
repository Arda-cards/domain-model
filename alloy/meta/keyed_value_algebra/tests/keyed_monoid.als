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
check unit_alg_scaleZeroValue {
  ringAxioms implies all s: Scalar | scale[s, zero] = zero
} for 3 but exactly 3 Scalar expect 0
