module conventions/notification_convergence/notification_convergence

/*
 * CONVENTION EXEMPLAR — CONVERGENT/NOTIFICATION (the B1 matrix's fire-and-forget class).
 * Canon: the B1 matrix + domain-log-kit §standard-laws; realized at scale in the demand R7
 * withdrawal listener and the order module's receipt accrual (`receiptsSettledAt`).
 *
 * THE SHAPE: an EMITTER commits and notifies post-commit, fire-and-forget — it cannot fix a
 * miss. A LISTENER converges: it applies a reaction kind on its own log, IDEMPOTENTLY (keyed
 * by the notifying occurrence's identity — runtime: the notifying record's rId), and a
 * runtime SELF-HEAL PROBE is the recovery floor for lost notifications. Consequences:
 *   - The reaction's idempotency is a LAW (at most one committed reaction per notification).
 *   - The MISSED-NOTIFICATION WINDOW IS LEGAL — emitted, not yet reacted; witnessed SAT.
 *   - Quiescence ("every emission has its reaction") is t-PARAMETERIZED — witnessed settled,
 *     legally false in the window, watched by the probe, NEVER a fact.
 *   - The SAME reaction kind serves the notification path, the manual repair, and the
 *     probe's re-drive — one kind, three drivers.
 *
 * THE EXEMPLAR: a Source pings; a Mirror reflects each ping exactly once. Both subjects
 * share the file; in core the notification crosses a module boundary on the observer channel.
 */

open meta/profiles/domain_log
open meta/kernel
open meta/subject_log/subject_log[Source, SourceRec] as xlog
open meta/subject_log/subject_log[Mirror, MirrorRec] as mlog

// ── the EMITTER ─────────────────────────────────────────────────────────────────────────────────
sig Source extends Scoped {}
fact SourceRefs { all s: Source | no s.dataRefs }
sig SourceRec extends Snapshot { srcPings: set PingOcc }   // its own committed pings (audit read)
fact SourceRecExtensional { all disj a, b: SourceRec | a.srcPings != b.srcPings }

sig StartSourceOcc extends xlog/SubjectOcc {} { bindings = subject }
/** Ping — the notifying commit: the EMISSION rides this occurrence's identity (runtime: the
    committed record's rId is the notification key). */
sig PingOcc extends xlog/SubjectOcc {} { bindings = subject }

// ── the LISTENER ────────────────────────────────────────────────────────────────────────────────
sig Mirror extends Scoped { watches: one EntityId }   // → Source (immutable structure)
fact MirrorRefs { all m: Mirror | m.dataRefs = m.watches }
fact MirrorWatchTyped { all m: Mirror | let s = resolve[m.watches] | some s implies s in Source }

sig MirrorRec extends Snapshot { mSeen: set PingOcc }   // the accumulated reactions
fact MirrorRecExtensional { all disj a, b: MirrorRec | a.mSeen != b.mSeen }

sig StartMirrorOcc extends mlog/SubjectOcc {} { bindings = subject }
/** Reflect — THE REACTION KIND: notification-driven, manual repair, and the probe's re-drive
    are all THIS kind; idempotency is keyed by the notifying occurrence (`ping`). */
sig ReflectOcc extends mlog/SubjectOcc { ping: one PingOcc } { bindings = subject + ping }

// ── reason-precise admission ────────────────────────────────────────────────────────────────────
one sig RAlreadyStarted, RNotStarted, RForeignPing, RDuplicate extends Reason {}

pred startedBeforeX[o: xlog/SubjectOcc] {
  some b: xlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
pred startedBeforeM[o: mlog/SubjectOcc] {
  some b: mlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
fun xPre[o: xlog/SubjectOcc]: lone SourceRec { o.pre & SourceRec }
fun mPre[o: mlog/SubjectOcc]: lone MirrorRec { o.pre & MirrorRec }

fun startSourceViol[o: StartSourceOcc]: set Reason { startedBeforeX[o] => RAlreadyStarted else none }
fun pingViol[o: PingOcc]: set Reason { (not startedBeforeX[o]) => RNotStarted else none }
fun startMirrorViol[o: StartMirrorOcc]: set Reason { startedBeforeM[o] => RAlreadyStarted else none }
/** THE IDEMPOTENCY GUARD: reflect only committed pings of the WATCHED source, at most once —
    the duplicate no-op is a typed refusal on the reaction's own log. */
fun reflectViol[o: ReflectOcc]: set Reason {
  ((not startedBeforeM[o]) => RNotStarted else none)
  + ((not committed[o.ping] or o.ping.subject != resolve[o.subject.watches]
      or not precedes[o.ping.tick, o.tick]) => RForeignPing else none)
  + ((o.ping in mPre[o].mSeen) => RDuplicate else none)
}

fact AdmissionWitness {
  all o: StartSourceOcc | (o.admission = Accepted iff no startSourceViol[o]) and (o.admission in Rejected implies o.admission.because = startSourceViol[o])
  all o: PingOcc        | (o.admission = Accepted iff no pingViol[o])        and (o.admission in Rejected implies o.admission.because = pingViol[o])
  all o: StartMirrorOcc | (o.admission = Accepted iff no startMirrorViol[o]) and (o.admission in Rejected implies o.admission.because = startMirrorViol[o])
  all o: ReflectOcc     | (o.admission = Accepted iff no reflectViol[o])     and (o.admission in Rejected implies o.admission.because = reflectViol[o])
}

// ── spine adoption + effects ────────────────────────────────────────────────────────────────────
fact SourceChain { xlog/chained }
fact MirrorChain { mlog/chained }

fun xPost[o: xlog/SubjectOcc]: lone SourceRec { o.post & SourceRec }
fun mPost[o: mlog/SubjectOcc]: lone MirrorRec { o.post & MirrorRec }

fact EffectWitness {
  all o: StartSourceOcc | committed[o] implies no xPost[o].srcPings
  all o: PingOcc        | committed[o] implies xPost[o].srcPings = xPre[o].srcPings + o
  all o: StartMirrorOcc | committed[o] implies no mPost[o].mSeen
  all o: ReflectOcc     | committed[o] implies mPost[o].mSeen = mPre[o].mSeen + o.ping
}

// ── reads ───────────────────────────────────────────────────────────────────────────────────────
fun seenAt[m: Mirror, t: Tick]: set PingOcc { mlog/recordAt[m, t].mSeen }

// ── the convention's laws ───────────────────────────────────────────────────────────────────────
/** reflectIdempotent — AT MOST ONE committed reaction per notification per mirror (the
    duplicate guard's theorem; runtime: the notificationId/rId no-op). */
pred reflectIdempotent {
  all m: Mirror, p: PingOcc | lone { o: ReflectOcc | committed[o] and o.subject = m and o.ping = p }
}

/** reflectSound — a mirror only ever accumulates committed pings of ITS source, and the
    accumulation only grows (no reaction un-reflects). */
pred reflectSound {
  all m: Mirror, t: Tick, p: seenAt[m, t] | committed[p] and p.subject = resolve[m.watches]
  all m: Mirror, t1, t2: Tick | notAfter[t1, t2] implies seenAt[m, t1] in seenAt[m, t2]
}

/** settledAt — the QUIESCENCE law, t-PARAMETERIZED (never a fact, NOT in guarantees): every
    committed ping at-or-before `t` is reflected by `t`. Legally FALSE in the
    missed-notification window; the runtime SELF-HEAL PROBE watches it and re-drives the
    reaction kind. */
pred settledAt[m: Mirror, t: Tick] {
  all p: PingOcc | (committed[p] and p.subject = resolve[m.watches] and notAfter[p.tick, t])
    implies p in seenAt[m, t]
}

/** guarantees — the exemplar's promise. */
pred guarantees { reflectIdempotent and reflectSound }
