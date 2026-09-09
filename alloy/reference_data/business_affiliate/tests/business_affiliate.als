module reference_data/business_affiliate/tests/business_affiliate

open meta/kernel
open reference_data/business_affiliate/business_affiliate_implementation

/*
 * Business-affiliate-module verification (LOG-CARRIED since DT-023 cut 7b). The cross-module
 * pin chains (item supply vendor pin, order supplier binding, receiver carrier) are verified
 * from the consumer sides. Content axiom gets witnesses (joint satisfiability); lifecycle
 * laws get CHECKS (theorems of the guards + effects) — the item suite's shape, one module
 * over.
 */

// ── content witnesses ───────────────────────────────────────────────────────────────────────────

// The module loads: an affiliate with a committed Create carrying a VENDOR role exists.
run unit_ba_coherent {
  some o: CreateBaOcc | committed[o] and some r: o.roles | r.role = VENDOR
} for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// A single affiliate version can bear several roles of different types (VENDOR + CARRIER…).
run unit_ba_multiRole {
  some o: CreateBaOcc, disj r1, r2: BusinessRole |
    committed[o] and r1 in o.roles and r2 in o.roles and r1.role != r2.role
} for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// Role ownership is exclusive across HISTORIES (C1 axiom regression) — UNSAT = holds.
check unit_ba_roleOwnership {
  no r: BusinessRole | some disj b1, b2: BusinessAffiliate | r in baRolesOf[b1] and r in baRolesOf[b2]
} for 6 but 4 Tick, 4 Snapshot, 4 Occurrence expect 0

// ── DT-023 cut 7b: the lifecycle (R1) ──────────────────────────────────────────────────────────

// The full arc: Create (live) → Update (live, roles changed) → Delete (retired). One
// affiliate, three committed occurrences; the read API tracks the statuses.
run unit_ba_lifecycleArc {
  some b: BusinessAffiliate, c: CreateBaOcc, u: UpdateBaOcc, d: RetireBaOcc {
    c.subject = b and u.subject = b and d.subject = b
    committed[c] and committed[u] and committed[d]
    precedes[c.tick, u.tick] and precedes[u.tick, d.tick]
    baLiveAt[b, u.tick] and not baLiveAt[b, d.tick]
    u.post.sRoles != c.post.sRoles
  }
} for 6 but 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// The lifecycle shape is a THEOREM of the guards + effects — UNSAT = holds.
check unit_ba_lifecycleShape { baLifecycleShape } for 6 but 6 Tick, 5 Snapshot, 5 Occurrence expect 0

// Reason-precise refusal: mutating a retired affiliate refuses with exactly RBaRetired.
run unit_ba_retiredMutateRefused {
  some d: RetireBaOcc, u: UpdateBaOcc {
    committed[d] and u.subject = d.subject and precedes[d.tick, u.tick]
    u.admission in Rejected and u.admission.because = RBaRetired
  }
} for 6 but 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// ── DT-023 cut 7b: version pins (R3) ───────────────────────────────────────────────────────────

// A pinnable version exists: current at t and Live — what an introducing consumer may pin.
run unit_ba_versionPinnable {
  some p: BaOcc, t: Tick | baPinnableAt[p, t]
} for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// The pinned read survives retirement (the grandfather half, module-side): a version pinned
// while live still serves its content after the affiliate retires.
run unit_ba_pinSurvivesRetirement {
  some p: BaOcc, t1, t2: Tick {
    baPinnableAt[p, t1]
    precedes[t1, t2] and not baLiveAt[p.subject, t2]
    some p.post
  }
} for 6 but 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// The role-selector agreement shape is satisfiable against a pinned version: a VENDOR
// selector into a pinnable version's membership (the dissolved-handle form's witness).
run unit_ba_roleSelectorWitness {
  some p: BaOcc, r: BusinessRole, t: Tick |
    baPinnableAt[p, t] and roleSelectorAgrees[p, r, VENDOR]
} for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// ── DT-030 retire cut (2026-09-09): terminality and the tombstone ────────────────────────────────
assert unit_ba_nothingAfterRetire {
  all r: RetireBaOcc, o: CreateBaOcc + UpdateBaOcc + RetireBaOcc | (committed[r] and committed[o] and o.subject = r.subject) implies not precedes[r.tick, o.tick]
}
check unit_ba_nothingAfterRetire for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 0
assert unit_ba_retireIsTombstone { all r: RetireBaOcc | committed[r] implies (r.post = r.pre and not baLiveAt[r.subject, r.tick]) }
check unit_ba_retireIsTombstone for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 0
