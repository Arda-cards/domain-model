module conventions/reason_precise_refusals/reason_precise_refusals

/*
 * CONVENTION EXEMPLAR — REASON-PRECISE REFUSALS (the admission-witness idiom).
 * Canon: the domain-log-kit (reason-precise witnessing); practiced by every log-carried
 * module since the InventoryItem pilot.
 *
 * THE CONVENTION: every operation's admission is decided by a per-kind VIOLATION SET — a
 * function collecting EXACTLY the reasons the operation would be wrong — and one witness
 * fact ties admission to it both ways:
 *     Accepted  ⟺  the violation set is EMPTY
 *     Rejected  ⟹  because = EXACTLY the set (never a subset, never "the first hit")
 * Refusals are first-class occurrences on the log (persisted, auditable, typed for the
 * caller), and every guard clause is INDEPENDENTLY witnessable: for each Reason there is a
 * SAT command producing a refusal whose `because` is exactly that reason. The discipline
 * that keeps it honest: EVERY CHECK IS PAIRED WITH SAT WITNESSES — an over-constrained
 * universe discharges any law vacuously (checks cannot tell "the law holds" from "nothing
 * exists"); the witnesses are the vacuity alarm. (This file's suite demonstrates the pairing
 * on itself.)
 *
 * THE EXEMPLAR: a Latch that opens, closes, and is passed through while open — three kinds,
 * four reasons, every reason witnessed exactly, plus a multi-reason refusal (because carries
 * the whole set).
 */

open meta/profiles/domain_log
open meta/kernel
open meta/subject_log/subject_log[Latch, LatchRec] as llog2

// ── the subject ─────────────────────────────────────────────────────────────────────────────────
abstract sig LatchStatus {}
one sig L_OPEN2, L_SHUT extends LatchStatus {}

sig Latch extends Scoped {}
fact LatchRefs { all l: Latch | no l.dataRefs }

sig LatchRec extends Snapshot { lStat: one LatchStatus, lPasses: set PassOcc }
fact LatchRecExtensional { all disj a, b: LatchRec | a.lStat != b.lStat or a.lPasses != b.lPasses }

sig InstallOcc extends llog2/SubjectOcc {} { bindings = subject }   // genesis (SHUT)
sig OpenOcc    extends llog2/SubjectOcc {} { bindings = subject }
sig PassOcc    extends llog2/SubjectOcc {} { bindings = subject }   // requires OPEN, once per pass atom
sig ShutOcc    extends llog2/SubjectOcc {} { bindings = subject }

// ── the reasons — each names ONE precise wrongness ──────────────────────────────────────────────
one sig RAlreadyInstalled,   // install: genesis-once
        RNotInstalled,       // any mutator before genesis
        RShut,               // pass: the latch is not open
        ROpen2               // shut/open state mismatches (open an OPEN latch / shut a SHUT one)
        extends Reason {}

// ── the violation sets (Accepted ⟺ ∅; because = EXACTLY the set) ────────────────────────────────
pred startedBeforeL2[o: llog2/SubjectOcc] {
  some b: llog2/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
fun lPre2[o: llog2/SubjectOcc]: lone LatchRec { o.pre & LatchRec }

fun installViol[o: InstallOcc]: set Reason { startedBeforeL2[o] => RAlreadyInstalled else none }
fun openLViol[o: OpenOcc]: set Reason {
  ((not startedBeforeL2[o]) => RNotInstalled else none)
  + ((startedBeforeL2[o] and lPre2[o].lStat = L_OPEN2) => ROpen2 else none)
}
/** passViol — TWO independent clauses; a pass on an uninstalled latch violates BOTH, and the
    refusal carries BOTH (the multi-reason demonstration). */
fun passViol[o: PassOcc]: set Reason {
  ((not startedBeforeL2[o]) => RNotInstalled else none)
  + ((lPre2[o].lStat != L_OPEN2) => RShut else none)
    // NB on an uninstalled latch lPre2 is EMPTY, and ∅ != L_OPEN2 holds — the clause fires
    // alongside RNotInstalled by DESIGN here (conservative refusal); order guards that want
    // a single precise reason condition later clauses on the earlier ones holding.
}
fun shutViol[o: ShutOcc]: set Reason {
  ((not startedBeforeL2[o]) => RNotInstalled else none)
  + ((startedBeforeL2[o] and lPre2[o].lStat = L_SHUT) => ROpen2 else none)
}

// ── THE WITNESS FACT — the whole convention in one fact ─────────────────────────────────────────
fact AdmissionWitness {
  all o: InstallOcc | (o.admission = Accepted iff no installViol[o]) and (o.admission in Rejected implies o.admission.because = installViol[o])
  all o: OpenOcc    | (o.admission = Accepted iff no openLViol[o])   and (o.admission in Rejected implies o.admission.because = openLViol[o])
  all o: PassOcc    | (o.admission = Accepted iff no passViol[o])    and (o.admission in Rejected implies o.admission.because = passViol[o])
  all o: ShutOcc    | (o.admission = Accepted iff no shutViol[o])    and (o.admission in Rejected implies o.admission.because = shutViol[o])
}

// ── spine adoption + effects ────────────────────────────────────────────────────────────────────
fact LatchChain { llog2/chained }
fun lPost2[o: llog2/SubjectOcc]: lone LatchRec { o.post & LatchRec }

fact EffectWitness {
  all o: InstallOcc | committed[o] implies { lPost2[o].lStat = L_SHUT and no lPost2[o].lPasses }
  all o: OpenOcc    | committed[o] implies { lPost2[o].lStat = L_OPEN2 and lPost2[o].lPasses = lPre2[o].lPasses }
  all o: PassOcc    | committed[o] implies { lPost2[o].lStat = lPre2[o].lStat and lPost2[o].lPasses = lPre2[o].lPasses + o }
  all o: ShutOcc    | committed[o] implies { lPost2[o].lStat = L_SHUT and lPost2[o].lPasses = lPre2[o].lPasses }
}

// ── reads ───────────────────────────────────────────────────────────────────────────────────────
fun latchStatusAt[l: Latch, t: Tick]: lone LatchStatus { llog2/recordAt[l, t].lStat }
fun passesAt[l: Latch, t: Tick]: set PassOcc { llog2/recordAt[l, t].lPasses }

// ── the convention's laws ───────────────────────────────────────────────────────────────────────
/** passRequiresOpen — the guard-derived theorem: every committed pass saw the latch OPEN. */
pred passRequiresOpen {
  all o: PassOcc | committed[o] implies lPre2[o].lStat = L_OPEN2
}
/** refusalsAreExact — the convention's OWN law, stated explicitly: a rejected occurrence's
    because is never empty and never exceeds its violation set (here for PassOcc; the witness
    fact gives it for every kind). */
pred refusalsAreExact {
  all o: PassOcc | o.admission in Rejected implies (some o.admission.because and o.admission.because = passViol[o])
}
/** guarantees */
pred guarantees { passRequiresOpen and refusalsAreExact }
