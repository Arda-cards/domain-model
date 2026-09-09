module soak/lemmas/reference_data_dynamics

/*
 * SOAK tier — the VERSION-DYNAMICS LEMMA root (DT-023 Q-D / DT-024, closing pass 7c):
 * prove the reference-data lifecycle + pin laws WIDE here, ONCE — multiple items and
 * affiliates each with a REAL multi-version log (Creates, Updates, Deletes coexisting) —
 * so every other soak root may take the CREATED-ONLY SLICE (each reference-data subject
 * carries exactly its Create; no Update/Delete atoms) with this root as the justification.
 * The slice is sound because the operational modules' laws read reference data only
 * through the pin/liveness API verified here; version dynamics never interleave with
 * operational choreography except through those reads. `make soak` only.
 */

open reference_data/item/item_implementation
open reference_data/business_affiliate/business_affiliate_implementation
open reference_data/staff/staff_implementation

// The item lifecycle shape at MULTI-SUBJECT, MULTI-VERSION scopes.
assert soak_rd_itemLifecycleShape { itemLifecycleShape }
check soak_rd_itemLifecycleShape for 6 but 5 Int, 3 Scalar,
      3 Item, 4 ItemSupply, 3 BusinessAffiliate, 4 BusinessRole, 2 StaffMember,
      12 Occurrence, 14 EntityId, 10 Tick, 12 Snapshot expect 0

// The affiliate lifecycle shape, same widths.
assert soak_rd_baLifecycleShape { baLifecycleShape }
check soak_rd_baLifecycleShape for 6 but 5 Int, 3 Scalar,
      3 Item, 4 ItemSupply, 3 BusinessAffiliate, 4 BusinessRole, 2 StaffMember,
      12 Occurrence, 14 EntityId, 10 Tick, 12 Snapshot expect 0

// Pinned-vs-floating DIVERGENCE is expressible at width (the drift witness the pin form
// exists for): a pin taken at t1 whose subject's CURRENT version at t2 differs — the pinned
// read stays on p.post while the floating read has moved (SAT = the boundary is real).
run soak_rd_pinnedFloatingDiverge {
  some p: ItemOcc, t1, t2: Tick {
    itemPinnableAt[p, t1]
    precedes[t1, t2]
    some itemVersionAt[p.subject, t2] and itemVersionAt[p.subject, t2] != p
  }
} for 6 but 5 Int, 3 Scalar,
      3 Item, 4 ItemSupply, 2 BusinessAffiliate, 3 BusinessRole, 2 StaffMember,
      12 Occurrence, 14 EntityId, 10 Tick, 12 Snapshot expect 1

// Currency is single-valued under dynamics: at any tick a subject has at most one current
// version (UNSAT = holds) — the read the floating semantics depend on.
assert soak_rd_currentUnique {
  all i: Item, t: Tick | lone itemVersionAt[i, t]
  all b: BusinessAffiliate, t: Tick | lone baVersionAt[b, t]
}
check soak_rd_currentUnique for 6 but 5 Int, 3 Scalar,
      3 Item, 4 ItemSupply, 3 BusinessAffiliate, 4 BusinessRole, 2 StaffMember,
      12 Occurrence, 14 EntityId, 10 Tick, 12 Snapshot expect 0

// SAT companion (anti-vacuity): a universe where an item AND an affiliate each carry a full
// Create → Update → Delete arc SIMULTANEOUSLY, with a supply row pinned mid-history.
run soak_rd_dynamicsCompanion {
  some i: Item, c: CreateItemOcc, u: UpdateItemOcc, d: RetireItemOcc |
    c.subject = i and u.subject = i and d.subject = i
    and committed[c] and committed[u] and committed[d]
  some b: BusinessAffiliate, c2: CreateBaOcc, u2: UpdateBaOcc, d2: RetireBaOcc |
    c2.subject = b and u2.subject = b and d2.subject = b
    and committed[c2] and committed[u2] and committed[d2]
  some s: ItemSupply | some s.supplierPin
} for 6 but 5 Int, 3 Scalar,
      2 Item, 3 ItemSupply, 2 BusinessAffiliate, 3 BusinessRole, 1 StaffMember,
      12 Occurrence, 14 EntityId, 10 Tick, 12 Snapshot expect 1
