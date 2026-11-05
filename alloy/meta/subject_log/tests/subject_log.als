module meta/subject_log/tests/subject_log

open meta/action/stateful
open meta/subject_log/subject_log[Widget, WidgetState] as wl
open meta/activation/activation   // the activation every row cites (DT-015 D1 to D3)

/*
 * Suite for the subject-log SPINE (DT-015 Q5 extraction), exercised on a minimal local
 * instantiation: a Widget whose record carries one Int level, with a single SetLevel operation
 * (guard: non-negative). Verifies exactly what the spine OWNS — the chaining law, LOCF reads,
 * and the refusals-read-but-don't-write discipline; kinds/guards/effects are the consumer's
 * (three real ones: the InventoryItem, InventoryPool, and CardCycle logs).
 */

sig Widget {}
sig WidgetState extends Snapshot { level: one Int }
fact WidgetStateExtensional { all disj a, b: WidgetState | a.level != b.level }

one sig RNegative extends Reason {}

sig SetLevelOcc extends wl/SubjectOcc { to: one Int } { bindings = subject + to }

one sig WidgetService extends Service {}
fact SpineAdopted { wl/chained and wl/commitAlwaysAccepts }
fact WidgetActivated { activated[WidgetService, wl/SubjectOcc] }   // DT-015 R2: beside the spine adoption
fun setViol[o: SetLevelOcc]: set Reason {
  ((o.to < 0) => RNegative else none)
}
fact SetLevelWitness {
  all o: SetLevelOcc | (o.admission = Accepted iff no setViol[o])
    and (o.admission in Rejected implies o.admission.because = setViol[o])
}
fact SetLevelEffect { all o: SetLevelOcc | committed[o] implies o.post.level = o.to }

// ── witnesses ───────────────────────────────────────────────────────────────────────────────────
// Two committed operations chain: the second reads the first's record; LOCF reads the second.
run unit_slog_chainLoads {
  some s: Widget, disj a, b: SetLevelOcc | {
    a.subject = s and b.subject = s and precedes[a.tick, b.tick]
    committed[a] and committed[b]
    b.pre = a.post
    wl/recordAt[s, b.tick] = b.post
  }
} for 5 but 4 Int expect 1

// A refusal READS the real record (unconditional chaining) yet has no post.
run unit_slog_refusalReadsReal {
  some s: Widget, a, r: SetLevelOcc | {
    a.subject = s and r.subject = s and precedes[a.tick, r.tick]
    committed[a] and refusedAtAdmission[r] and r.admission.because = RNegative
    r.pre = a.post and no r.post
  }
} for 5 but 4 Int expect 1

// ── theorems (check; UNSAT = holds) ─────────────────────────────────────────────────────────────
// The first occurrence on a subject reads nothing.
assert unit_slog_firstReadsNothing {
  all o: wl/SubjectOcc | no wl/priorOn[o] implies no o.pre
}
check unit_slog_firstReadsNothing for 5 but 4 Int expect 0

// LOCF: the as-of read at any occurrence's tick is the latest committed post at-or-before it.
assert unit_slog_locf {
  all o: wl/SubjectOcc | committed[o] implies wl/recordAt[o.subject, o.tick] = o.post
}
check unit_slog_locf for 5 but 4 Int expect 0

// Refusals contribute nothing: the read just after a refusal equals the read just before it.
assert unit_slog_refusalContributesNothing {
  all o: wl/SubjectOcc | refusedAtAdmission[o] implies
    wl/recordAt[o.subject, o.tick] = wl/lastTouch[o.subject, o.tick].post
    and (no wl/lastTouch[o.subject, o.tick] or committed[wl/lastTouch[o.subject, o.tick]])
}
check unit_slog_refusalContributesNothing for 5 but 4 Int expect 0

// THE STATE FUNCTION (1:1 in the subject→record direction): once a subject has committed
// history, it has EXACTLY ONE current record at every instant — recordAt is a total function of
// (started subject, tick). Derived, not assumed: lastTouch is unique (one occurrence per tick,
// ticks totally ordered) and a committed occurrence always has a post (PostOnlyIfCommitted).
// NB the converse direction is deliberately NOT 1:1 — records are extensional VALUES, shared
// across subjects and times (two subjects in identical conditions share one record atom).
assert unit_slog_recordIsFunctionOnceStarted {
  all s: Widget, t: Tick |
    (wl/startedAt[s, t] implies one wl/recordAt[s, t])
    and (not wl/startedAt[s, t] implies no wl/recordAt[s, t])
}
check unit_slog_recordIsFunctionOnceStarted for 5 but 4 Int expect 0

// The chaining thread is committed-only: an occurrence's pre is always a COMMITTED predecessor's post.
assert unit_slog_threadIsCommitted {
  all o: wl/SubjectOcc | some o.pre implies committed[wl/priorOn[o]]
}
check unit_slog_threadIsCommitted for 5 but 4 Int expect 0


// ── the activation (DT-015 D1 to D3): the rows cite the act that wrote them; no per-row origin law ──────────────────
// THE SIBLING WITNESS (MP, Journal 192741): one activation writes TWO committed operations on ONE widget. RED on the
// tree before DT-015: `ArcheUnique` (DT-029 Q8) forbade two committed rows on one subject citing one origin (UNSAT).
run unit_slog_siblingEffectsOneActivation {
  some a: Call, w: Widget, disj x, y: SetLevelOcc |
    committed[a] and committed[x] and committed[y] and x.subject = w and y.subject = w and x.arche = a and y.arche = a
} for 5 but 4 Int expect 1

// One activation may span TWO subjects (a transfer's paired rows, SAMWISE-S1) — unchanged by the cut.
run unit_slog_oneActivationTwoSubjects {
  some a: Call, disj x, y: SetLevelOcc | committed[a] and committed[x] and committed[y] and x.subject != y.subject
    and x.arche = a and y.arche = a
} for 5 but 4 Int expect 1

// A refused operation cites a refused activation and still reads the real record (chaining is unconditional).
run unit_slog_refusedRowCitesRefusedActivation {
  some a: Call, s: Widget, o, r: SetLevelOcc | committed[o] and o.subject = s and r.subject = s and precedes[o.tick, r.tick]
    and refusedAtAdmission[a] and r.arche = a and refusedAtAdmission[r] and r.pre = o.post
} for 5 but 4 Int expect 1
