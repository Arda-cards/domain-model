module meta/subject_log/tests/lifecycle

open meta/action/stateful
open meta/subject_log/subject_log[Widget, WidgetState] as wl
open meta/subject_log/lifecycle[Widget, WidgetState] as lc     // same params ⇒ lc/*Occ extend wl/SubjectOcc

/*
 * Suite for the LIFECYCLE shapes (DT-030, plan of record 2026-09-09) on the spine root's minimal instantiation: a Widget
 * with one Int level; Create / SetLevel (a Mutate) / Retire. Verifies exactly what the module OWNS: the liveness read,
 * the three generic arms mapped to the adopter's atoms, the tombstone effect, the terminality theorem, and the
 * witness-by-shape idiom compiling and behaving (one witness per shape, a domain arm composed in).
 */

sig Widget {}
sig WidgetState extends Snapshot { level: one Int }
fact WidgetStateExtensional { all disj a, b: WidgetState | a.level != b.level }

one sig RWidgetStarted, RWidgetClosed, RNegative extends Reason {}

sig CreateWidgetOcc extends lc/CreateOcc {} { bindings = subject }
sig SetLevelOcc extends lc/MutateOcc { to: one Int } { bindings = subject + to }
sig RetireWidgetOcc extends lc/RetireOcc {} { bindings = subject }

fact SpineAdopted { wl/chained and wl/commitAlwaysAccepts }

// ── the witness, ONCE PER SHAPE (the idiom the adopters restate to) ─────────────────────────────
fun domainViol[o: lc/MutateOcc]: set Reason { ((o & SetLevelOcc).to < 0) => RNegative else none }
fact Witness {
  all o: lc/CreateOcc | let v = lc/createViol[o, RWidgetStarted] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/MutateOcc | let v = lc/liveViol[o, RWidgetClosed] + domainViol[o] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/RetireOcc | let v = lc/retireViol[o, RWidgetClosed] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
}
fact Effects {
  all o: CreateWidgetOcc | committed[o] implies o.post.level = 0
  all o: SetLevelOcc     | committed[o] implies o.post.level = o.to
}

// ── witnesses ───────────────────────────────────────────────────────────────────────────────────
// A full life: create, mutate, retire — all commit, in order, and the read after the retire is the tombstone's record.
run unit_lc_fullLife {
  some s: Widget, c: CreateWidgetOcc, m: SetLevelOcc, r: RetireWidgetOcc | {
    c.subject = s and m.subject = s and r.subject = s
    precedes[c.tick, m.tick] and precedes[m.tick, r.tick]
    committed[c] and committed[m] and committed[r]
    wl/recordAt[s, r.tick] = m.post
  }
} for 5 but 4 Int expect 1
// A second create on a started subject is refused with the adopter's started atom.
run unit_lc_doubleCreateRefused {
  some s: Widget, disj c1, c2: CreateWidgetOcc | c1.subject = s and c2.subject = s and precedes[c1.tick, c2.tick]
    and committed[c1] and refusedAtAdmission[c2] and c2.admission.because = RWidgetStarted
} for 5 but 4 Int expect 1
// A mutation before any create is refused closed (not live: never started).
run unit_lc_mutateBeforeCreateRefused {
  some s: Widget, m: SetLevelOcc | m.subject = s and m.to >= 0 and (no o: wl/SubjectOcc - m | o.subject = s and committed[o] and precedes[o.tick, m.tick])
    and refusedAtAdmission[m] and m.admission.because = RWidgetClosed
} for 5 but 4 Int expect 1
// A mutation after a committed retire is refused closed; the domain arm composes (negative level after retire: both atoms).
run unit_lc_mutateAfterRetireRefused {
  some s: Widget, c: CreateWidgetOcc, r: RetireWidgetOcc, m: SetLevelOcc | {
    c.subject = s and r.subject = s and m.subject = s
    precedes[c.tick, r.tick] and precedes[r.tick, m.tick]
    committed[c] and committed[r] and m.to < 0
    refusedAtAdmission[m] and m.admission.because = RWidgetClosed + RNegative
  }
} for 5 but 4 Int expect 1
// A second retire is refused closed — never a no-op.
run unit_lc_secondRetireRefused {
  some s: Widget, c: CreateWidgetOcc, disj r1, r2: RetireWidgetOcc | {
    c.subject = s and r1.subject = s and r2.subject = s
    precedes[c.tick, r1.tick] and precedes[r1.tick, r2.tick]
    committed[c] and committed[r1] and refusedAtAdmission[r2] and r2.admission.because = RWidgetClosed
  }
} for 5 but 4 Int expect 1

// ── laws ────────────────────────────────────────────────────────────────────────────────────────
// Terminality: nothing commits after a committed retire (the theorem the adopters check, here on the minimal adopter).
check unit_lc_nothingAfterRetire { lc/nothingAfterRetire } for 5 but 4 Int expect 0
// The tombstone: a committed retire changes nothing and the as-of read at its tick is its pre.
assert unit_lc_tombstone { all o: lc/RetireOcc | committed[o] implies (o.post = o.pre and wl/recordAt[o.subject, o.tick] = o.pre) }
check unit_lc_tombstone for 5 but 4 Int expect 0
// A committed mutation has a pre (never the first row, never the tombstone).
check unit_lc_mutateHasPre { lc/mutateHasPre } for 5 but 4 Int expect 0
// A committed create is the first row: nothing committed on the subject precedes it.
assert unit_lc_createIsFirst { all o: lc/CreateOcc | committed[o] implies not lc/startedBefore[o] }
check unit_lc_createIsFirst for 5 but 4 Int expect 0
// A refused occurrence of any shape writes nothing.
assert unit_lc_refusalWritesNothing { all o: wl/SubjectOcc | refusedAtAdmission[o] implies no o.post }
check unit_lc_refusalWritesNothing for 5 but 4 Int expect 0
