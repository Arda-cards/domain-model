module meta/subject_log/tests/affirm

open meta/action/stateful
open meta/subject_log/subject_log[Widget, WidgetState] as wl
open meta/subject_log/affirm[Widget, WidgetState] as aff      // same params ⇒ aff/AffirmOcc extends wl/SubjectOcc
open meta/subject_log/affirm_reasons                          // RStaleAffirmation

/*
 * Suite for the AFFIRM kind (DT-030, MP 2026-09-09) on the spine root's minimal instantiation: a Widget whose record
 * carries one Int level and a SetLevel operation. Verifies exactly what the affirm module OWNS: a committed affirmation
 * leaves the record unchanged and becomes `lastTouch`; a stale affirmation (of a non-current version) is refused
 * RStaleAffirmation; an affirmation on a never-created subject is refused with the adopter's atom; a committed
 * affirmation always affirms the current record.
 */

sig Widget {}
sig WidgetState extends Snapshot { level: one Int }
fact WidgetStateExtensional { all disj a, b: WidgetState | a.level != b.level }

one sig RNegative, RNotCreated extends Reason {}

sig SetLevelOcc extends wl/SubjectOcc { to: one Int } { bindings = subject + to }
fact SpineAdopted { wl/chained and wl/commitAlwaysAccepts }
fun setViol[o: SetLevelOcc]: set Reason { ((o.to < 0) => RNegative else none) }
fact SetLevelWitness {
  all o: SetLevelOcc | (o.admission = Accepted iff no setViol[o])
    and (o.admission in Rejected implies o.admission.because = setViol[o])
}
fact SetLevelEffect { all o: SetLevelOcc | committed[o] implies o.post.level = o.to }

fact AffirmAdopted { aff/affirmAdmissionWitness[RNotCreated] }

// ── witnesses ───────────────────────────────────────────────────────────────────────────────────
// A committed SetLevel, then a committed affirmation of its record: the record is unchanged and LOCF still reads it.
run unit_aff_affirmLoads {
  some s: Widget, a: SetLevelOcc, f: aff/AffirmOcc | {
    a.subject = s and f.subject = s and precedes[a.tick, f.tick]
    committed[a] and committed[f] and f.affirmed = a.post
    wl/recordAt[s, f.tick] = a.post
  }
} for 5 but 4 Int expect 1

// A stale affirmation — of a version that a later committed operation superseded — is refused RStaleAffirmation.
run unit_aff_staleRefused {
  some s: Widget, disj a, b: SetLevelOcc, f: aff/AffirmOcc | {
    a.subject = s and b.subject = s and f.subject = s
    precedes[a.tick, b.tick] and precedes[b.tick, f.tick]
    committed[a] and committed[b] and f.affirmed = a.post
    refusedAtAdmission[f] and f.admission.because = RStaleAffirmation
  }
} for 5 but 4 Int expect 1

// An affirmation on a subject with no committed history is refused with the adopter's not-created atom.
run unit_aff_noSubjectRefused {
  some s: Widget, f: aff/AffirmOcc | {
    f.subject = s and no o: wl/SubjectOcc - f | o.subject = s and committed[o] and precedes[o.tick, f.tick]
    refusedAtAdmission[f] and f.admission.because = RNotCreated
  }
} for 5 but 4 Int expect 1

// ── laws ────────────────────────────────────────────────────────────────────────────────────────
// A committed affirmation changes nothing: its post is its pre, and the as-of read at its tick is its pre.
assert unit_aff_recordUnchanged {
  all o: aff/AffirmOcc | committed[o] implies (o.post = o.pre and wl/recordAt[o.subject, o.tick] = o.pre)
}
check unit_aff_recordUnchanged for 5 but 4 Int expect 0

// A committed affirmation IS the spine's `lastTouch` at its tick — the evidence pointer moves, the record does not.
assert unit_aff_lastTouchMoves {
  all o: aff/AffirmOcc | committed[o] implies wl/lastTouch[o.subject, o.tick] = o
}
check unit_aff_lastTouchMoves for 5 but 4 Int expect 0

// A committed affirmation always affirms the CURRENT record: "I checked and it is so" is never true of a stale version.
assert unit_aff_neverCommitsStale {
  all o: aff/AffirmOcc | committed[o] implies o.affirmed = o.pre
}
check unit_aff_neverCommitsStale for 5 but 4 Int expect 0

// A refused affirmation writes nothing (the spine's discipline holds for the new kind).
assert unit_aff_refusalWritesNothing {
  all o: aff/AffirmOcc | refusedAtAdmission[o] implies no o.post
}
check unit_aff_refusalWritesNothing for 5 but 4 Int expect 0
