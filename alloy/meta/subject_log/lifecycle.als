module meta/subject_log/lifecycle[Subject, Rec]

/*
 * LIFECYCLE — the opt-in SHAPE PARTITION of a subject log's kinds (DT-030; MP 2026-09-09, the plan of record in
 * workbook streams/samwise/model-changes-sequence.md; design: mutate-occ-abstract-supertype.md §7–§8, generic-retire-impact.md).
 *
 * Four shapes by EFFECT, never by verb: CREATE (the first row of a history), RETIRE (the tombstone: `post = pre`,
 * terminal — nothing commits on the subject after it), MUTATE (the record changes, or may), and AFFIRM (declared
 * beside this module in meta/subject_log/affirm: `post = pre`, a claim about a version). Three are declared here;
 * an adopter declares every concrete kind under one of them (`sig DeleteDemandOcc extends lc/RetireOcc`,
 * `abstract sig MemberOcc extends lc/MutateOcc`, …) and NEVER directly under `log/SubjectOcc` — tools/lifecycle-gate.py
 * enforces that, and asserts the adopter set, so a shape law never reads as true of all while true of some.
 *
 * WHAT THE MODULE OWNS (once, for every adopter): the liveness READ — a subject is live at an occurrence when it has
 * committed history strictly before and no committed retire strictly before (`liveAt`); the retire EFFECT
 * (`RetireEffect`); the three generic guard ARMS, each mapped by the adopter to ITS OWN atom (the spine idiom,
 * subject_log.als:59–74 — no atom is declared here): `createViol[o, rStarted]` (a create on a started subject),
 * `liveViol[o, rClosed]` (a mutation on a subject not live), `retireViol[o, rClosed]` (a retire on a subject not
 * live — the second retire is REFUSED, never a no-op). And the THEOREM every adopter checks, never asserts as a
 * fact: `nothingAfterRetire`.
 *
 * WHAT STAYS WITH THE ADOPTER: the atoms; the DOMAIN arms (`RFrozen`, `RBadState`, `RNotTerminal`, …); the
 * per-kind effects and frames (`Rec` is opaque here); the witness, now writable ONCE PER SHAPE:
 *   fun domainViol[o: lc/MutateOcc]: set Reason { (o in AdjustQtyOcc => adjustViol[o & AdjustQtyOcc] else none) + … }
 *   fact Witness { all o: lc/MutateOcc | let v = lc/liveViol[o, RDemandClosed] + domainViol[o] |
 *     (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v) … }
 * Records are VALUES (extensional), so a mutation that changes nothing has `post = pre` — legal; the model has no
 * law forcing `post != pre` (touch-as-affirmation-act.md §8 claim 3).
 *
 * SHAPE: open with the log's OWN parameters; this module rides the SAME spine instance (the affirm precedent):
 *   open meta/subject_log/lifecycle[DemandItem, DemandState] as lc
 * Alloy note (the throwaway of 2026-09-09, scratch/samwise/cut1/overload): a field declared on two sigs under
 * different shapes is read through a TYPED receiver or an explicit cast `(o & A).f + (o & B).f`; a read over the
 * bare union `A + B` is refused as ambiguous. Demand's `member` is the one instance in the tree.
 */

open meta/action/stateful                                // StatefulAction, committed, Reason; transitively Tick, precedes
open meta/subject_log/subject_log[Subject, Rec] as log   // the SPINE — same params ⇒ the adopter's instance

/** The three shapes declared here. Abstract: no atoms of their own; every concrete kind is one of them (or an Affirm). */
abstract sig CreateOcc extends log/SubjectOcc {}
abstract sig RetireOcc extends log/SubjectOcc {}
abstract sig MutateOcc extends log/SubjectOcc {}

// ── the liveness read, once ─────────────────────────────────────────────────────────────────────
/** startedBefore — the subject has committed history strictly before `o` (any kind). */
pred startedBefore[o: log/SubjectOcc] {
  some b: log/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
/** retiredBefore — a committed retire (tombstone) on the subject strictly before `o`. */
pred retiredBefore[o: log/SubjectOcc] {
  some b: RetireOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
/** liveAt — started and not retired, as `o` reads it. The SHAPE half of liveness; a domain's terminal statuses
    (COMPLETE, CANCELED, L_CLOSED, …) are the adopter's own arms beside this one. */
pred liveAt[o: log/SubjectOcc] { startedBefore[o] and not retiredBefore[o] }
/** liveSubjectAt — the SUBJECT-level read (for guards on references, pins, and reads as-of a tick): live at `t` iff it has
    a head at-or-before `t` and that head is not a retire. Equivalent to "started and not retired" under terminality; this
    is the form a runtime reads as `head.kind is not a retire kind` — the translated read of DT-030's D13 table. */
pred liveSubjectAt[s: Subject, t: Tick] { some log/lastTouch[s, t] and log/lastTouch[s, t] not in RetireOcc }

// ── the retire effect, once ─────────────────────────────────────────────────────────────────────
/** RetireEffect — the tombstone: a committed retire's `post` IS its `pre` (records are values; the row is the end of history). */
fact RetireEffect { all o: RetireOcc | committed[o] implies o.post = o.pre }

// ── the generic guard arms — CONDITIONS here, ATOMS the adopter's ─────────────────────────────
fun createViol[o: CreateOcc, rStarted: Reason]: set Reason { startedBefore[o] => rStarted else none }
fun liveViol[o: log/SubjectOcc, rClosed: Reason]: set Reason { (not liveAt[o]) => rClosed else none }
fun retireViol[o: RetireOcc, rClosed: Reason]: set Reason { liveViol[o, rClosed] }

// ── the CONDITION half of each generic arm, as a module LAW ─────────────────────────────────────
/** ShapeAdmission — a create on a started subject, a mutation on a subject not live, a retire on a subject not live:
    each is REJECTED. The atom it is rejected WITH stays the adopter's, named in its witness through the arms above
    (an adopter's exact-set witness that carries the arm is consistent with this fact; one that forgot the arm makes
    the forgotten instances impossible, so its own roots go loudly UNSAT — the forgetting cannot hide).
    WHY A FACT: an abstract shape left unextended in a root is, in Alloy, a concrete sig — a free kind with no witness at
    all. Found on the affirm root (2026-09-09): `lc/CreateOcc` had no extension there and committed after a retire.
    With this law, terminality (`nothingAfterRetire`) and `mutateHasPre` are theorems of the MODULE for every adopter
    whose kinds are all classified (tools/lifecycle-gate.py), not properties each adopter must remember. */
fact ShapeAdmission {
  all o: CreateOcc | startedBefore[o] implies o.admission in Rejected
  all o: MutateOcc | not liveAt[o]     implies o.admission in Rejected
  all o: RetireOcc | not liveAt[o]     implies o.admission in Rejected
}

// ── the theorems every adopter CHECKS (module theorems once all kinds are classified; a red is a classification gap) ──
/** nothingAfterRetire — terminality: no occurrence of any kind commits on a subject after its committed retire (needs the
    affirm module's own arm for affirmations — it has one). */
pred nothingAfterRetire { all o: log/SubjectOcc | committed[o] implies not retiredBefore[o] }
/** mutateHasPre — a committed mutation is never the first row and never the tombstone (a consequence of the arms, stated). */
pred mutateHasPre { all o: MutateOcc | committed[o] implies some o.pre }
