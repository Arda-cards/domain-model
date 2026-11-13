module reference_data/item/tests/uom_collapse
// Reflects dafny-domain src/reference-data/item/tests/uom-collapse-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

/*
 * Verification of the multi-unit UoM collapse (DT-009): `collapse(sch, q) = { each ↦ Σ_u q[u]·factor[u] }`.
 * Checks carry `ringAxioms` as a PREMISE and scope `exactly 3 Scalar` (= the field ℤ/3, no zero divisors)
 * so the abstract decimal behaves as a sound ring for the fold.
 */

open reference_data/item/uom_collapse

// EXISTENCE — a genuine TWO-unit collapse: two distinct non-each units fold into one non-zero `each` total.
run unit_collapse_loads {
  ringAxioms
  some sch: UomScheme, q: Quantity, disj u1, u2: Unit {
    u1 != Each and u2 != Each
    q.byUnit.Scalar = u1 + u2                 // exactly two (non-each) units in support
    hasGroup[sch, q]
    some collapse[sch, q][Each]               // a non-zero `each` total exists
  }
} for 6 but exactly 3 Scalar expect 1

// STRUCTURE — the collapse result is always single-key `each`.
check unit_collapse_eachKeyed {
  all sch: UomScheme, q: Quantity | collapse[sch, q].Scalar in Each
} for 6 expect 0

// BASE CASE — a single-unit collapse equals the existing `toEach` (ties the fold base to `uom/toEach`).
check unit_collapse_singleIsToEach {
  ringAxioms => all sch: UomScheme, q: Quantity, u: Unit |
    (q.byUnit.Scalar = u and hasGroup[sch, q]) =>
      collapse[sch, q][Each] = toEach[sch, u, q.byUnit[u]]
} for 6 but exactly 3 Scalar expect 0

// IDENTITY — collapsing a quantity already expressed in `each` returns its `each` amount unchanged.
check unit_collapse_eachIdentity {
  ringAxioms => all sch: UomScheme, q: Quantity |
    (q.byUnit.Scalar = Each and hasGroup[sch, q]) =>
      collapse[sch, q][Each] = q.byUnit[Each]
} for 6 but exactly 3 Scalar expect 0

// FOLD CORRECTNESS — when a two-unit total is non-zero, it equals the ring sum of the two per-unit
// `each`-contributions. (A canceling total folds to the empty map — the normal-form invariant, not an
// exception: the `each` key is simply absent.)
check unit_collapse_twoUnitFolds {
  ringAxioms => all sch: UomScheme, q: Quantity, disj u1, u2: Unit |
    (q.byUnit.Scalar = (u1 + u2) and hasGroup[sch, q] and some collapse[sch, q][Each]) =>
      collapse[sch, q][Each] =
        (q.byUnit[u1].smul[sch.factor[u1]]).splus[ q.byUnit[u2].smul[sch.factor[u2]] ]
} for 6 but exactly 3 Scalar expect 0

// CANCELLATION — two units whose contributions net to zero collapse to the EMPTY map (no `each` key):
// the normal-form drop, demonstrated positively.
run unit_collapse_cancels {
  ringAxioms
  some sch: UomScheme, q: Quantity, disj u1, u2: Unit {
    q.byUnit.Scalar = u1 + u2
    hasGroup[sch, q]
    no collapse[sch, q][Each]                 // the two `each`-contributions net to zero → dropped
  }
} for 6 but exactly 3 Scalar expect 1
