module meta/occurrence/occurrence

/*
 * Occurrence — something that happens: an entry in the LOG, at a position in MODEL TIME (`tick`).
 *
 * MINIMAL BY DESIGN (DT-011, 2026-07-02): the core carries ONLY the causal position. The domain-time
 * stamp (`at: Instant`) is the OPT-IN subset extension `meta/occurrence/timed` — most log reasoning
 * (chaining, projections, guards) never needs wall-clock time, and carrying it by default put the
 * whole Instant family (and the two-clock bridge premise) into every log universe. Open `timed` where
 * chronological reads (period bucketing, staleness, as-of-wall-time) are actually wanted.
 */

open meta/model_time/model_time   // Tick, precedes, follows, notAfter

/** Occurrence — something that happens: a model-time (causal) position in the log, with an
    optional free-text annotation of the act itself. */
abstract sig Occurrence {
  tick: one Tick,        // model time — WHERE in the causal order
  note: lone String,     // occurrence-level annotation (MP unification ruling, 2026-08-10):
                         //   an INERT, uninterpreted payload — no law may read its content.
                         //   Built-in String: ZERO atoms in any command without string
                         //   literals, so the whole log cone carries the seat for free.
                         //   Immutable with the occurrence (acts never change after commit).
                         //   Distinct from RECORD-carried notes (shared/note's `Note` atoms
                         //   on state records — LOCF-read, freeze-governed).
  arche: one Occurrence  // THE ACT THAT WROTE THIS ROW (DT-029 E1, "use arche across the board", MP 2026-08-28; TOTAL since
                         //   MP's D13 ruling A, 2026-09-03; the ACTIVATION since DT-015 D1, 2026-11-05, reflecting
                         //   dafny-domain src/meta/activation.dfy): an entity row cites the activation that wrote it; an
                         //   activation cites its caller's activation, or ITSELF when it is an origin — the arrival of a
                         //   cause from outside (`o.arche = o`, `selfInitiated`). The runtime's NOT-NULL `arche_id` column
                         //   carries the activation id (MP 3.1: no branch, no null). Which occurrences may be cited, and
                         //   which may self-cite, is `meta/activation/activation`'s (its two module facts); the kernel
                         //   states only the one universal truth below. No per-row uniqueness: one act may write several
                         //   rows on one subject (MP, Journal 192741; `ArcheUnique` left the spine, DT-015 D3). No root /
                         //   audit column ever exists (MP 3.2: the call tree is walkable through this one field).
}

/** Ticks linearize occurrences — at most one occurrence per tick — so the causal order is a strict
    total order on occurrences (not merely on the underlying ticks). */
fact OneOccurrencePerTick { all disj a, b: Occurrence | a.tick != b.tick }

/** occPrecedes — the causal (model-time) order lifted to occurrences. */
pred occPrecedes[a, b: Occurrence] { precedes[a.tick, b.tick] }

/** selfInitiated — the occurrences that cite THEMSELVES: no caller context. The self-loop is the ONE spelling
    of "self-initiated" — the field is total, like the runtime column (MP's D13 ruling A, 2026-09-03). Under
    `meta/activation/activation` these are exactly the ORIGINS: the self-citing activations (DT-015 D1). */
fun selfInitiated: set Occurrence { { o: Occurrence | o.arche = o } }

/** A CITED origin is STRICTLY earlier than the occurrence citing it: origins never point forward; the only
    occurrence an occurrence may cite at its own tick is itself (self-initiation, exempt below). Proper cycles
    are a THEOREM of strict precedence, checked in the tests (unit_occ_archeNoProperCycle), never a fact. The
    one universal, cheap truth about origins — everything else about `arche` is `meta/activation/activation`'s
    (DT-015 D1 to D3). */
fact ArcheOriginPrecedes { all o: Occurrence | o.arche != o implies precedes[o.arche.tick, o.tick] }
