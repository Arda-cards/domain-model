module reference_data/staff/tests/staff

/*
 * STAFF — module suite (DT-022 TQ-7(b) cut 6; LOG-CARRIED since DT-023 cut 7c). The
 * identity law keeps its check + boundary witness; the lifecycle gains the arc/shape/
 * refusal/pin family (the BA suite's shape, minus roles and minus Update — status-only
 * state, Update omitted as vacuous).
 */

open meta/kernel
open reference_data/staff/staff_implementation

/** unit_stf_loads — the module is jointly satisfiable with two committed-created members. */
pred unit_stf_loads {
  #StaffMember >= 2 and all s: StaffMember | some o: CreateStaffOcc | o.subject = s and committed[o]
}
run unit_stf_loads for 4 but 6 EntityId, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

/** unit_stf_nameUniqueInTenant — no two same-tenant members share a name (the law,
    restated as an assertion over the implementation). */
assert unit_stf_nameUniqueInTenant {
  all disj a, b: StaffMember | a.tenantId = b.tenantId implies a.name != b.name
}
check unit_stf_nameUniqueInTenant for 5 but 8 EntityId, 4 Tick, 4 Snapshot, 4 Occurrence expect 0

/** unit_stf_sameNameAcrossTenants — BOUNDARY: the SAME name legally recurs in two
    different tenants (uniqueness is tenant-scoped, not global). */
pred unit_stf_sameNameAcrossTenants {
  some disj a, b: StaffMember | a.tenantId != b.tenantId and a.name = b.name
}
run unit_stf_sameNameAcrossTenants for 4 but 6 EntityId, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// ── DT-023 cut 7c: the lifecycle (R1, Update omitted) ──────────────────────────────────────────

// The arc: Create (live) → Delete (retired); the read API tracks the statuses.
run unit_stf_lifecycleArc {
  some s: StaffMember, c: CreateStaffOcc, d: RetireStaffOcc {
    c.subject = s and d.subject = s
    committed[c] and committed[d]
    precedes[c.tick, d.tick]
    staffLiveAt[s, c.tick] and not staffLiveAt[s, d.tick]
  }
} for 5 but 5 Tick, 3 Snapshot, 3 Occurrence, 6 EntityId expect 1

// The lifecycle shape is a THEOREM of the guards + effects — UNSAT = holds.
check unit_stf_lifecycleShape { staffLifecycleShape } for 5 but 6 Tick, 5 Snapshot, 5 Occurrence, 8 EntityId expect 0

// Reason-precise refusal: deleting a retired member refuses with exactly RStaffRetired.
run unit_stf_retiredDeleteRefused {
  some d: RetireStaffOcc, d2: RetireStaffOcc {
    committed[d] and d2.subject = d.subject and precedes[d.tick, d2.tick]
    d2.admission in Rejected and d2.admission.because = RStaffRetired
  }
} for 5 but 5 Tick, 4 Snapshot, 3 Occurrence, 6 EntityId expect 1

// A pinnable version exists; and a pin survives retirement (the grandfather half).
run unit_stf_pinSurvivesRetirement {
  some p: StaffOcc, t1, t2: Tick {
    staffPinnableAt[p, t1]
    precedes[t1, t2] and not staffLiveAt[p.subject, t2]
    some p.post
  }
} for 5 but 5 Tick, 4 Snapshot, 3 Occurrence, 6 EntityId expect 1

// ── DT-030 retire cut (2026-09-09): terminality and the tombstone ────────────────────────────────
assert unit_staff_nothingAfterRetire {
  all r: RetireStaffOcc, o: CreateStaffOcc + RetireStaffOcc | (committed[r] and committed[o] and o.subject = r.subject) implies not precedes[r.tick, o.tick]
}
check unit_staff_nothingAfterRetire for 5 but 5 Tick, 4 Snapshot, 3 Occurrence, 6 EntityId expect 0
assert unit_staff_retireIsTombstone { all r: RetireStaffOcc | committed[r] implies (r.post = r.pre and not staffLiveAt[r.subject, r.tick]) }
check unit_staff_retireIsTombstone for 5 but 5 Tick, 4 Snapshot, 3 Occurrence, 6 EntityId expect 0
