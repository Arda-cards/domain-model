module meta/action/action

/*
 * Action — the execution of an activity, reified as an `Occurrence` in the Tick-ordered LOG
 * (DT-006, Layer 1 — structural ontology; dynamics deferred to Layer 2).
 *
 * READER'S MAP (one line each; the full anatomy, rationale, and decisions live in the workbook
 * design/meta/action — single source of truth; worked examples: ex15 guards/chaining, ex16 two
 * time models, ex17 snapshot chains):
 *  - STATE-AS-PROJECTION: no `World`, no domain `var` — state at tick t = a fold over
 *    `committedUpTo[t]`; a refused action contributes nothing (rollback is free).
 *  - `bindings: set univ` — the BINDING ENVIRONMENT: the quantifier prefix of the guarded formula
 *    ("∃ x such that guard(x) then effect(x)"); DERIVED per kind from named, TYPED binding fields.
 *  - ONE guard, `admission`, reads the pre-projection (`committedBefore`); an admitted action IS committed
 *    (MP, Journal 193772; TN-003 row 9: the post-commit check left with the Dafny spine, which has none).
 *  - WITNESSING PATTERN: guards are made evaluable per kind by a fact tying the stored verdict to
 *    a predicate — `all a: K | a.admission = Accepted iff kAdmissible[a]`.
 *  - The core is MINIMAL (DT-011): OPT-IN subset extensions add state snapshots
 *    (`meta/action/stateful` — where the Effect has its seat), the actor
 *    (`meta/action/attributed`, `by` — ABAC/provenance), and the domain-time stamp
 *    (`meta/occurrence/timed`, `at`). Open only what the model actually reads.
 */

open meta/occurrence/occurrence   // Occurrence (tick — the causal log position)
open meta/model_time/model_time   // Tick order vocabulary (precedes, notAfter)
open meta/action/outcome          // Decision, Accepted, Rejected, Reason

// ── anatomy ──────────────────────────────────────────────────────────────────────────────────────

/** Action — an executed activity, reified as an Occurrence (an entry in the log). */
abstract sig Action extends Occurrence {
  bindings:  set univ,           // the binding environment (quantifier prefix) — DERIVED from per-kind typed fields
  admission: one Decision        // the guard's verdict on the pre-projection: the action's outcome
}

// ── the two outcomes (they partition Action) ─────────────────────────────────────────────────────

/** committed — admitted (only committed actions contribute to the state projection). */
pred committed[a: Action] { a.admission = Accepted }

/** refusedAtAdmission — the first gate refused; the action was never attempted against a result. */
pred refusedAtAdmission[a: Action] { a.admission in Rejected }

/** refusalReasons — why a refused action did not take effect. */
fun refusalReasons[a: Action]: set Reason { a.admission.because }

// ── projection domains — the log prefixes state is folded over ───────────────────────────────────

/** committedBefore — the committed log STRICTLY before `t`: the PRE-projection domain every
    admission guard reads ("the state just before me"). */
fun committedBefore[t: Tick]: set Action { { a: Action | committed[a] and precedes[a.tick, t] } }

/** committedUpTo — the committed log at-or-before `t` (inclusive): the POST-projection domain —
    an action's own contribution is visible at its own tick. A state query after a chain of actions
    is "filter this by kind/bindings, then fold" (keyed_sum for levels, LOCF for last-write-wins,
    existsAt-style for existence). */
fun committedUpTo[t: Tick]: set Action { { a: Action | committed[a] and notAfter[a.tick, t] } }
