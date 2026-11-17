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
