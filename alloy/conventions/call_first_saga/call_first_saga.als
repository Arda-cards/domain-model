module conventions/call_first_saga/call_first_saga

/*
 * CONVENTION EXEMPLAR — the CONVERGENT/OPERATION CALL-FIRST SAGA (the B1 matrix's
 * cross-module Operation class). Canon: domain-log-kit §standard-laws + the B1 matrix
 * (work-board DT-016); realized at scale in operations/demand (R3/R8) and procurement/order
 * (attach/Submit gates).
 *
 * THE SHAPE: a caller needs a peer's state to advance. Cross-module means NEVER ATOMIC — so
 * the caller invokes the PEER operation FIRST, reads its typed response, and only then
 * commits its own row, whose ADMISSION GUARD is the saga's COMMIT GATE: it re-checks the
 * peer's current state. Consequences the model embraces:
 *   - The commit-gate law is a THEOREM of the guard ("a committed step saw the peer at the
 *     expected state") — no cross-log enforcement facts exist.
 *   - IN-FLIGHT INTERMEDIATES ARE LEGAL (the crash window between the peer call and the
 *     caller's commit) — witnessed SAT, never outlawed.
 *   - CONVERGENCE IS THE CALLER'S: retry the commit (the guard re-checks idempotently), or
 *     COMPENSATE with an existing peer operation.
 *   - The QUIESCENCE law is t-PARAMETERIZED — witnessed on settled traces, watched by the
 *     runtime probe, NEVER a global fact (that would outlaw the legal in-flight states).
 *
 * THE EXEMPLAR: a Job activates over a Slot. The saga: acquire the Slot FIRST (peer op),
 * then commit Activate (whose guard gates on the slot being HELD). Both subjects share this
 * file for compactness; in core models they live in DIFFERENT modules and the "call" is the
 * peer's service interface — the doc carries the mapping.
 */

open meta/profiles/domain_log
open meta/kernel
open meta/subject_log/subject_log[Slot, SlotRec] as slog
open meta/subject_log/subject_log[Job, JobRec] as jlog

// ── the PEER: a Slot that can be held ───────────────────────────────────────────────────────────
abstract sig SlotStatus {}
one sig S_FREE, S_HELD extends SlotStatus {}

sig Slot extends Scoped {}
fact SlotRefs { all s: Slot | no s.dataRefs }
sig SlotRec extends Snapshot { sStat: one SlotStatus }
fact SlotRecExtensional { all disj a, b: SlotRec | a.sStat != b.sStat }

sig AddSlotOcc  extends slog/SubjectOcc {} { bindings = subject }   // genesis (FREE)
sig AcquireOcc  extends slog/SubjectOcc {} { bindings = subject }   // the saga's FIRST leg
sig ReleaseOcc2 extends slog/SubjectOcc {} { bindings = subject }   // the COMPENSATOR

fun slotStatusAt[s: Slot, t: Tick]: lone SlotStatus { slog/recordAt[s, t].sStat }

// ── the CALLER: a Job that activates over a held slot ───────────────────────────────────────────
abstract sig JobStatus {}
one sig J_IDLE, J_ACTIVE extends JobStatus {}

sig Job extends Scoped {}
fact JobRefs { all j: Job | no j.dataRefs }
sig JobRec extends Snapshot { jStat: one JobStatus, jSlot: lone EntityId }
fact JobRecExtensional { all disj a, b: JobRec | a.jStat != b.jStat or a.jSlot != b.jSlot }
fact JobSlotTyped { all r: JobRec | let s = resolve[r.jSlot] | some s implies s in Slot }

sig OpenJobOcc  extends jlog/SubjectOcc {} { bindings = subject }
/** Activate — the CALLER's commit; its guard IS the saga's commit gate. */
sig ActivateOcc extends jlog/SubjectOcc { slot: one EntityId } { bindings = subject + slot }

fun jobStatusAt[j: Job, t: Tick]: lone JobStatus { jlog/recordAt[j, t].jStat }

// ── reason-precise admission ────────────────────────────────────────────────────────────────────
one sig RAlreadyStarted, RNotStarted, RSlotBusy, RSlotFree, RSlotNotHeld, RBadState extends Reason {}

pred startedBeforeS[o: slog/SubjectOcc] {
  some b: slog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
pred startedBeforeJ[o: jlog/SubjectOcc] {
  some b: jlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
fun sPre[o: slog/SubjectOcc]: lone SlotRec { o.pre & SlotRec }
fun jPre[o: jlog/SubjectOcc]: lone JobRec { o.pre & JobRec }

fun addSlotViol[o: AddSlotOcc]: set Reason { startedBeforeS[o] => RAlreadyStarted else none }
fun acquireViol[o: AcquireOcc]: set Reason {
  ((not startedBeforeS[o]) => RNotStarted else none)
  + ((sPre[o].sStat = S_HELD) => RSlotBusy else none)
}
fun releaseViol[o: ReleaseOcc2]: set Reason {
  ((not startedBeforeS[o]) => RNotStarted else none)
  + ((sPre[o].sStat = S_FREE) => RSlotFree else none)
}
fun openJobViol[o: OpenJobOcc]: set Reason { startedBeforeJ[o] => RAlreadyStarted else none }
/** THE COMMIT GATE: the caller's guard re-checks the PEER's current state (strictly-before
    reads — OneOccurrencePerTick keeps `o` itself off the peer log's tick). */
fun activateViol[o: ActivateOcc]: set Reason {
  ((not startedBeforeJ[o]) => RNotStarted else none)
  + ((jPre[o].jStat != J_IDLE) => RBadState else none)
  + ((let s = resolve[o.slot] & Slot | no s or slotStatusAt[s, o.tick] != S_HELD)
     => RSlotNotHeld else none)
}

fact AdmissionWitness {
  all o: AddSlotOcc  | (o.admission = Accepted iff no addSlotViol[o])  and (o.admission in Rejected implies o.admission.because = addSlotViol[o])
  all o: AcquireOcc  | (o.admission = Accepted iff no acquireViol[o])  and (o.admission in Rejected implies o.admission.because = acquireViol[o])
  all o: ReleaseOcc2 | (o.admission = Accepted iff no releaseViol[o])  and (o.admission in Rejected implies o.admission.because = releaseViol[o])
  all o: OpenJobOcc  | (o.admission = Accepted iff no openJobViol[o])  and (o.admission in Rejected implies o.admission.because = openJobViol[o])
  all o: ActivateOcc | (o.admission = Accepted iff no activateViol[o]) and (o.admission in Rejected implies o.admission.because = activateViol[o])
}

// ── spine adoption + effects (NO cross-log enforcement facts — the guard IS the gate) ───────────
fact SlotChain { slog/chained }
fact JobChain  { jlog/chained }

fun sPost[o: slog/SubjectOcc]: lone SlotRec { o.post & SlotRec }
fun jPost[o: jlog/SubjectOcc]: lone JobRec { o.post & JobRec }

fact EffectWitness {
  all o: AddSlotOcc  | committed[o] implies sPost[o].sStat = S_FREE
  all o: AcquireOcc  | committed[o] implies sPost[o].sStat = S_HELD
  all o: ReleaseOcc2 | committed[o] implies sPost[o].sStat = S_FREE
  all o: OpenJobOcc  | committed[o] implies { jPost[o].jStat = J_IDLE and no jPost[o].jSlot }
  all o: ActivateOcc | committed[o] implies { jPost[o].jStat = J_ACTIVE and jPost[o].jSlot = o.slot }
}

// ── the convention's laws ───────────────────────────────────────────────────────────────────────
/** activateRequiresHeld — the COMMIT-GATE THEOREM: a committed Activate saw its slot HELD.
    Derived from the guard; no enforcement fact anywhere. */
pred activateRequiresHeld {
  all o: ActivateOcc | committed[o] implies slotStatusAt[resolve[o.slot] & Slot, o.tick] = S_HELD
}

/** alignedAt — the QUIESCENCE law, t-PARAMETERIZED (never a fact, NOT in guarantees): at a
    settled moment, held slots and active jobs correspond. Legally FALSE in the crash window
    (slot acquired, activation not yet committed) — the runtime probe's watch condition. */
pred alignedAt[t: Tick] {
  all s: Slot | slotStatusAt[s, t] = S_HELD implies
    (some j: Job | jobStatusAt[j, t] = J_ACTIVE and resolve[jlog/recordAt[j, t].jSlot] = s)
}

/** guarantees — the exemplar's promise (the gate theorem only; quiescence is watched, not
    promised). */
pred guarantees { activateRequiresHeld }
