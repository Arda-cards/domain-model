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

// ── R02-D24.1 (model): a business role's kind is fixed at birth (MP, COORDINATOR-Q357, Option C) ──
// The role IDENTITY (`BusinessRole`) carries the kind it was born with; each role VERSION
// (`BusinessRoleVersion`) states the kind of its write (`vKind`) next to its payload (`detail`).
// An Update that states a version whose `vKind` differs from its identity's kind is refused
// with exactly `RRoleKindFixed`; every committed version agrees with its identity.

// RED-first: an Update stating another kind for an existing role identity refuses with exactly RRoleKindFixed.
run unit_ba_roleKindChangeRefused {
  some c: CreateBaOcc, u: UpdateBaOcc, v: u.roleVersions {
    committed[c] and c.subject = u.subject and precedes[c.tick, u.tick]
    v.vKind != v.of.role
    u.admission in Rejected and u.admission.because = RRoleKindFixed
  }
} for 6 but 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// RED-first: the law is a THEOREM of the guard + the Create fact — UNSAT = holds.
check unit_ba_roleKindFixedAtBirth { roleKindFixedAtBirth } for 6 but 6 Tick, 5 Snapshot, 5 Occurrence expect 0

// Control: an Update that changes only the payload of an existing role (same identity, same kind) is admitted.
run unit_ba_roleVersionDetailChangeAdmitted {
  some c: CreateBaOcc, u: UpdateBaOcc, r: BusinessRole, v1, v2: BusinessRoleVersion {
    committed[c] and committed[u] and c.subject = u.subject and precedes[c.tick, u.tick]
    v1 in c.roleVersions and v2 in u.roleVersions
    v1.of = r and v2.of = r and v1.vKind = r.role and v2.vKind = r.role
    v1.detail != v2.detail
    v1 not in u.post.sRoleVersions and v2 in u.post.sRoleVersions   // the transition: the new version replaces the old one in the state
  }
} for 6 but 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// Control: replacing a role by a NEW identity of another kind (a removal plus an addition) is admitted.
run unit_ba_replaceByNewIdAdmitted {
  some c: CreateBaOcc, u: UpdateBaOcc, disj r1, r2: BusinessRole {
    committed[c] and committed[u] and c.subject = u.subject and precedes[c.tick, u.tick]
    r1 in c.roles and r1.role = VENDOR
    u.roles = r2 and r2.role = CARRIER
    r1 not in u.post.sRoles
  }
} for 6 but 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// ── R02-D24.1 review fixes (Copilot's review of domain-model#5): the state holds exactly the versions written ──
// RED-first: a committed write's post state holds exactly the versions the write states (not only their identities).
check unit_ba_postHoldsExactlyTheWrittenVersions {
  all o: BaWriteOcc | committed[o] implies o.post.sRoleVersions = o.roleVersions
} for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 0

// RED-first: every version in a committed post state states its identity's kind (the law, read over states).
check unit_ba_committedStatesAgreeOnKind {
  all o: BaOcc | committed[o] implies (all v: o.post.sRoleVersions | v.vKind = v.of.role)
} for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 0

// RED-first: at most one version per role identity in a committed write and in a committed post state.
check unit_ba_oneVersionPerRole {
  all o: BaWriteOcc | committed[o] implies (no disj v1, v2: o.roleVersions | v1.of = v2.of)
  all o: BaOcc | committed[o] implies (no disj v1, v2: o.post.sRoleVersions | v1.of = v2.of)
} for 6 but 4 Tick, 3 Snapshot, 3 Occurrence expect 0

// RED-first: two writes of one affiliate that differ only in a version's detail have different bindings.
run unit_ba_bindingsDistinguishVersions {
  some disj o1, o2: UpdateBaOcc {
    o1.subject = o2.subject and o1.roles = o2.roles and o1.roleVersions != o2.roleVersions
    o1.bindings != o2.bindings
  }
} for 6 but 4 Tick, 4 Snapshot, 3 Occurrence expect 1
