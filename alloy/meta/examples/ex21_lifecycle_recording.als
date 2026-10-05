module meta/examples/ex21_lifecycle_recording

open meta/action/stateful
open meta/subject_log/subject_log[Folio, FolioState] as flog
open meta/subject_log/lifecycle[Folio, FolioState] as lc      // same params ⇒ lc/*Occ extend flog/SubjectOcc

/*
 * ex21 — LIFECYCLE SHAPES + THE RECORDING LAW (`meta/subject_log/lifecycle`): what a runtime PERSISTS
 * of a refusal. Hotel flavor, ex19's folio grown a lifecycle: OPEN (the genesis), CHARGE (a mutation),
 * CLOSE (the retire). Every refusal is `refusedAtAdmission`; only a refusal with a HOST row is
 * `lc/recorded` — a refused charge on an open OR closed folio (the record, tombstone included, carries
 * the REFUSED row); never a refused OPEN (a first open has no folio row yet, a second open is a
 * conflict answered with no row), never a charge on a folio that was never opened. The theorem
 * `lc/noRecordedRefusalWithoutGenesis` is what every adopter checks.
 *
 * RECIPE (on top of ex19's):
 *   1. open meta/subject_log/lifecycle[YourEntity, YourStateRecord] as lc   (beside the subject_log open)
 *   2. sig <Genesis>Occ extends lc/CreateOcc; sig <Mutation>Occ extends lc/MutateOcc; sig <Retire>Occ extends lc/RetireOcc
 *   3. the witness fact per SHAPE: lc/createViol[o, rStarted] · lc/liveViol[o, rClosed] + domainViol[o] · lc/retireViol[o, rClosed]
 *   4. read what persisted with lc/recorded[o]; check lc/noRecordedRefusalWithoutGenesis in your root.
 */

sig Folio {}
sig FolioState extends Snapshot { balance: one Int }
fact FolioStateExtensional { all disj a, b: FolioState | a.balance != b.balance }

one sig RFolioOpen, RFolioClosed, RNonPositiveCharge extends Reason {}

sig OpenFolioOcc  extends lc/CreateOcc {} { bindings = subject }
sig ChargeOcc     extends lc/MutateOcc { amount: one Int } { bindings = subject + amount }
sig CloseFolioOcc extends lc/RetireOcc {} { bindings = subject }

fact SpineAdopted { flog/chained and flog/commitAlwaysAccepts }

fun domainViol[o: lc/MutateOcc]: set Reason { ((o & ChargeOcc).amount <= 0) => RNonPositiveCharge else none }
fact Witness {
  all o: lc/CreateOcc | let v = lc/createViol[o, RFolioOpen] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/MutateOcc | let v = lc/liveViol[o, RFolioClosed] + domainViol[o] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/RetireOcc | let v = lc/retireViol[o, RFolioClosed] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
}
fact Effects {
  all o: OpenFolioOcc | committed[o] implies o.post.balance = 0
  all o: ChargeOcc    | committed[o] implies o.post.balance = o.pre.balance.plus[o.amount]
}

// A refused charge on a folio that was never opened: refused, NOT recorded (no row can host it).
run ex21_refusedChargeBeforeOpenNotRecorded {
  some o: ChargeOcc | refusedAtAdmission[o] and no o.pre and not lc/recorded[o]
} for 5 but 4 Int expect 1
// A refused SECOND open: refused (RFolioOpen), NOT recorded — a conflict answered with no row, though the folio has a record.
run ex21_refusedSecondOpenNotRecorded {
  some disj a, b: OpenFolioOcc | committed[a] and b.subject = a.subject and precedes[a.tick, b.tick]
    and refusedAtAdmission[b] and b.admission.because = RFolioOpen and not lc/recorded[b]
} for 5 but 4 Int expect 1
// A refused charge on an OPEN folio (non-positive amount): refused AND recorded — the REFUSED row the ledger keeps.
run ex21_refusedChargeOnOpenFolioRecorded {
  some o: ChargeOcc | refusedAtAdmission[o] and lc/liveAt[o] and lc/recorded[o]
} for 5 but 4 Int expect 1
// A refused charge on a CLOSED folio: refused (RFolioClosed) AND recorded — the tombstone is still a record.
run ex21_refusedChargeOnClosedFolioRecorded {
  some o: ChargeOcc | refusedAtAdmission[o] and lc/retiredBefore[o] and lc/recorded[o]
} for 5 but 4 Int expect 1
// THE THEOREM: nothing recorded-but-refused on a folio without a committed genesis.
check ex21_noRecordedRefusalWithoutGenesis { lc/noRecordedRefusalWithoutGenesis } for 5 but 4 Int expect 0
