module reference_data/staff/staff_implementation

/*
 * STAFF — IMPLEMENTATION (DT-017). Log-carried since DT-023 cut 7c: lifecycle machinery
 * (chaining, reason-precise admission, effects); the identity law stays an asserted axiom.
 */

open reference_data/staff/staff_contracts
open reference_data/staff/staff_types as st   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[st/StaffMember, st/StaffState] as stlog  // same params ⇒ the SAME spine instance

// ── the spine adoptions ─────────────────────────────────────────────────────────────────────────
fact StaffChain { stlog/chained }
fact StaffCommitPolicy { stlog/commitAlwaysAccepts }

// ── reason-precise admission (the witnessing idiom) ─────────────────────────────────────────────
/** createStaffViol — Create refuses only an already-created subject. */
fun createStaffViol[o: CreateStaffOcc]: set Reason { (some o.pre => RStaffExists else none) }
/** deleteStaffViol — Delete refuses an uncreated or retired subject. */
fun deleteStaffViol[o: DeleteStaffOcc]: set Reason {
  ((no o.pre) => RStaffNotCreated else none)
  + ((some o.pre and (o.pre & StaffState).sStatus = RD_RETIRED) => RStaffRetired else none)
}

fact StaffAdmissionWitnessed {
  all o: CreateStaffOcc | (o.admission = Accepted iff no createStaffViol[o]) and (o.admission in Rejected implies o.admission.because = createStaffViol[o])
  all o: DeleteStaffOcc | (o.admission = Accepted iff no deleteStaffViol[o]) and (o.admission in Rejected implies o.admission.because = deleteStaffViol[o])
}

// ── effects ─────────────────────────────────────────────────────────────────────────────────────
fact StaffEffects {
  all o: CreateStaffOcc | committed[o] implies (o.post & StaffState).sStatus = RD_LIVE
  all o: DeleteStaffOcc | committed[o] implies (o.post & StaffState).sStatus = RD_RETIRED
}

// ── the content axiom (C1 — nothing deeper derives it) ─────────────────────────────────────────
fact StaffContentLaws { staffNameUnique }
