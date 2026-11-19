module meta/subject_log/tests/subject_log
// Reflects dafny-domain src/meta/tests/trace-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

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
fact SpineAdopted { wl/chained }
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
