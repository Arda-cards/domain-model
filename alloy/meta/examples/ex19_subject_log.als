module meta/examples/ex19_subject_log

open meta/action/stateful
open meta/subject_log/subject_log[Folio, FolioState] as flog

/*
 * ex19 — THE SUBJECT-LOG SPINE (DT-015 Q5): the fastest way to give an entity an operation log.
 * Hotel flavor: a guest FOLIO whose record carries a running balance; two operations — Charge
 * (any positive amount) and Settle (must clear the EXACT balance; anything else is refused with a
 * precise reason). The spine supplies the chaining law and the LOCF reads; this file writes ONLY
 * the domain: the kinds, the guards (witnessing idiom), and the effects.
 *
 * RECIPE (what you copy for a real module):
 *   1. open meta/subject_log/subject_log[YourEntity, YourStateRecord] as log
 *   2. sig <Operation>Occ extends log/SubjectOcc { params } { bindings = subject + params }
 *   3. fact { log/chained }
 *   4. per-kind violation funs + the two-line witness fact (reason-precise refusals)
 *   5. per-kind effect frames on committed occurrences
 *   6. read with log/recordAt[s, t]; define YOUR closure/liveness on log/lastTouch.
 */

sig Folio {}
sig FolioState extends Snapshot { balance: one Int }
fact FolioStateExtensional { all disj a, b: FolioState | a.balance != b.balance }

one sig RNonPositiveCharge, RWrongAmount extends Reason {}

sig ChargeOcc extends flog/SubjectOcc { amount: one Int } { bindings = subject + amount }
sig SettleOcc extends flog/SubjectOcc { paid: one Int }   { bindings = subject + paid }

fact SpineAdopted { flog/chained }

fun chargeViol[o: ChargeOcc]: set Reason { (o.amount <= 0) => RNonPositiveCharge else none }
fun settleViol[o: SettleOcc]: set Reason { (o.paid != o.pre.balance) => RWrongAmount else none }
fact Witnessing {
  all o: ChargeOcc | (o.admission = Accepted iff no chargeViol[o]) and (o.admission in Rejected implies o.admission.because = chargeViol[o])
  all o: SettleOcc | (o.admission = Accepted iff no settleViol[o]) and (o.admission in Rejected implies o.admission.because = settleViol[o])
}
fact Effects {
  all o: ChargeOcc | committed[o] implies o.post.balance = plus[o.pre.balance, o.amount]
  all o: SettleOcc | committed[o] implies o.post.balance = 0
}
// (First occurrence has no pre: a first Charge reads balance none — pin the opening explicitly.)
fact OpeningCharge { all o: ChargeOcc | no o.pre implies (committed[o] implies o.post.balance = o.amount) }

// A charge → charge → settle story, read back through the spine.
run ex19_folioStory {
  some f: Folio, c1, c2: ChargeOcc, s: SettleOcc | {
    c1.subject = f and c2.subject = f and s.subject = f
    precedes[c1.tick, c2.tick] and precedes[c2.tick, s.tick]
    committed[c1] and committed[c2] and committed[s]
    flog/recordAt[f, s.tick].balance = 0
  }
} for 5 but 5 Int expect 1

// A wrong-amount settle is refused with exactly RWrongAmount — and contributes nothing.
run ex19_wrongSettleRefused {
  some s: SettleOcc | refusedAtAdmission[s] and s.admission.because = RWrongAmount
} for 5 but 5 Int expect 1

// The ledger read is always the last committed post (the spine's LOCF, on this domain).
assert ex19_ledgerIsLocf {
  all o: flog/SubjectOcc | committed[o] implies flog/recordAt[o.subject, o.tick] = o.post
}
check ex19_ledgerIsLocf for 5 but 5 Int expect 0
