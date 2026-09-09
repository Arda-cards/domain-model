module reference_data/staff/staff_contracts

/*
 * STAFF — CONTRACTS (DT-017). Log-carried since DT-023 cut 7c: the identity law stays an
 * AXIOM; the lifecycle laws are THEOREMS of the guards + effects; chaining is the spine's.
 * Consistency class: ATOMIC (single-module).
 */

open reference_data/staff/staff_types as st
open meta/subject_log/subject_log[st/StaffMember, st/StaffState] as stlog  // same params ⇒ the SAME spine instance

// ── C1: name uniqueness (identity-carried — unchanged by the conversion) ────────────────────────
/** staffNameUnique — a staff member's name is unique WITHIN its tenant (MP ruling,
    DT-022 TQ-7(b) follow-up, 2026-08-08); the same name may recur across tenants. */
pred staffNameUnique {
  all disj a, b: StaffMember | a.tenantId = b.tenantId implies a.name != b.name
}

// ── C2: the lifecycle shape (DT-023 R1, Update omitted — theorem of guards + effects) ──────────
/** A committed first occurrence is the Create (and Creates are only ever first);
    retirement is TERMINAL. */
pred staffLifecycleShape {
  all o: StaffOcc | committed[o] implies {
    ((no stlog/priorOn[o]) iff o in CreateStaffOcc)
    (some stlog/priorOn[o] implies stlog/priorOn[o] not in RetireStaffOcc)   // the prior head is never the tombstone (terminality)
  }
}

// ── C3: the log is chained (the spine's law, re-published for mock consumers) ──────────────────
pred staffLogChained { stlog/chained }

/** guarantees — everything a consumer may assume of this module. */
pred guarantees { staffNameUnique and staffLifecycleShape and staffLogChained }
