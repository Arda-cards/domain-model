module meta/subject_log/affirm[Subject, Rec]

/*
 * AFFIRM — the opt-in AFFIRMATION kind for a subject log (DT-030; MP 2026-09-09: "Accept the new proposed model row
 * and adopt it in the model"; design: workbook streams/samwise/touch-as-affirmation-act.md).
 *
 * An authoritative source affirms, at a time, that the subject's value is UNCHANGED. It is an ACT — an occurrence
 * with an author, a tick and an outcome — with NO domain effect (`post = pre`, the same record atom: records are
 * values) and an INFORMATION effect: evidence of the value, resetting its staleness (DT-010). The spine's LOCF read
 * (`recordAt`) is an ASSUMPTION that a value persists between occurrences; an affirmation is the OBSERVATION that
 * evidences it, and `lastTouch` — the spine's own name for the evidence pointer — then IS the affirmation.
 *
 * NOT the bitemporal mechanism's `touch`: a re-stamped row copying the previous envelope is a system version, not an
 * act, below this model's resolution (streams/samwise/system-versions-are-not-acts.md). The act is named `Affirm` so
 * the two never share a word; under D13 the runtime verb is `affirm`.
 *
 * SHAPE (the intent_log shape): open with the log's OWN parameters and this module rides the SAME spine instance:
 *   open meta/subject_log/affirm[InventoryPool, PoolState] as aff
 *   fact PoolAffirmWitness { aff/affirmAdmissionWitness[RPoolNotCreated] }   // the adopter names its not-created atom
 * WHAT STAYS WITH THE ADOPTER (the spine idiom, subject_log.als:59–74): the not-created atom (its own taxonomy).
 * The stale atom is the pattern layer's, declared once in meta/subject_log/affirm_reasons. No adoption in the tree
 * until MP's DT-010 word (inventory_pool first).
 */

open meta/action/stateful                                // Snapshot, StatefulAction, committed, refusedAtAdmission, Reason
open meta/subject_log/subject_log[Subject, Rec] as log   // the SPINE — same params ⇒ the adopter's instance (item_types precedent)
open meta/subject_log/affirm_reasons                     // RStaleAffirmation

/** AffirmOcc — "I checked and it is so": `affirmed` is the VERSION the source affirms (the version-pin shape, DT-023):
    a claim about a specific value, which is what makes the occurrence evidence rather than a blind ping. */
sig AffirmOcc extends log/SubjectOcc { affirmed: one Rec } { bindings = subject + affirmed }

/** The effect: none on the record — the committed affirmation's `post` IS its `pre`. The occurrence is the evidence. */
fact AffirmEffect { all o: AffirmOcc | committed[o] implies o.post = o.pre }

/** Guard CONDITIONS (general layer); the atoms follow the spine idiom. */
pred affirmNoSubject[o: AffirmOcc] { no o.pre }                            // no record at this position: never created
pred affirmStale[o: AffirmOcc]     { some o.pre and o.affirmed != o.pre }   // the affirmed version is not the current record

fun affirmViol[o: AffirmOcc, rNotCreated: Reason]: set Reason {
  (affirmNoSubject[o] => rNotCreated else none) + (affirmStale[o] => RStaleAffirmation else none)
}
/** The admission witness, once, parameterized by the adopter's not-created atom (the two-line idiom). */
pred affirmAdmissionWitness[rNotCreated: Reason] {
  all o: AffirmOcc | (o.admission = Accepted iff no affirmViol[o, rNotCreated])
    and (o.admission in Rejected implies o.admission.because = affirmViol[o, rNotCreated])
}
