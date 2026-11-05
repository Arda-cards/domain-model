module reference_data/staff/staff_implementation

/*
 * STAFF — IMPLEMENTATION (DT-017). Log-carried since DT-023 cut 7c: lifecycle machinery
 * (chaining, reason-precise admission, effects); the identity law stays an asserted axiom.
 */

open reference_data/staff/staff_contracts
open reference_data/staff/staff_types as st   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[st/StaffMember, st/StaffState] as stlog  // same params ⇒ the SAME spine instance
open meta/subject_log/lifecycle[st/StaffMember, st/StaffState] as lc      // same params ⇒ the SAME shapes instance
open meta/activation/activation   // the activation every row cites (DT-015 D1 to D3)

// ── the spine adoptions ─────────────────────────────────────────────────────────────────────────
fact StaffChain { stlog/chained }
one sig StaffService extends Service {}   // DT-015 R2: the service's activation log, adopted beside the spine
fact StaffActivated { activated[StaffService, stlog/SubjectOcc] }

// ── reason-precise admission (the witnessing idiom) ─────────────────────────────────────────────
/** createStaffViol — Create refuses an already-created subject (the generic create arm, the module's atom) and a name a CREATED
    member of the tenant already bears (RStaffNameTaken — QA704 Q4 (a): the content fact `staffNameUnique` as the arm it is in
    dafny-domain src/reference-data/staff/staff.dfy `NameFreeInTenant`; the law is its theorem over created members). */
fun createStaffViol[o: CreateStaffOcc]: set Reason {
  lc/createViol[o, RStaffExists]
  + ((some c: CreateStaffOcc | committed[c] and precedes[c.tick, o.tick] and c.subject != o.subject
        and c.subject.tenantId = o.subject.tenantId and c.subject.name = o.subject.name) => RStaffNameTaken else none)
}
/** retireStaffViol — Retire refuses an uncreated or already-retired subject (the generic liveness conditions, the
    module's two atoms — the adopter may split the closed atom in two). */
fun retireStaffViol[o: RetireStaffOcc]: set Reason {
  ((not lc/startedBefore[o]) => RStaffNotCreated else none)
  + (lc/retiredBefore[o] => RStaffRetired else none)
}

fact StaffAdmissionWitnessed {
  all o: CreateStaffOcc | (o.admission = Accepted iff no createStaffViol[o]) and (o.admission in Rejected implies o.admission.because = createStaffViol[o])
  all o: RetireStaffOcc | (o.admission = Accepted iff no retireStaffViol[o]) and (o.admission in Rejected implies o.admission.because = retireStaffViol[o])
}

// ── effects: none to state — the record is fieldless; the retire's tombstone is the lifecycle module's `RetireEffect` ──

// (C1, name uniqueness, is a THEOREM of the RStaffNameTaken arm above since QA704 Q4 (a): tests/staff.als unit_stf_nameUniqueInTenant.)
