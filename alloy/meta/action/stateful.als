module meta/action/stateful

/*
 * StatefulAction — the OPTIONAL snapshot-carrying extension of the Action framework (DT-006 build
 * prep, 2026-07-02): open this ONLY for action kinds whose occurrences record the state they read
 * and produced (the as-of-read pattern — open #3). The core `meta/action/action` stays
 * state-agnostic; this module is to it what keyed_order is to keyed_monoid.
 *
 * This is where the EFFECT gets a visible seat in the anatomy: the pipeline is
 *     admission reads `pre`  →  the Effect constrains (pre, post),
 * and "the Effect of kind K" is precisely the constraint K's transition core places on the pair
 * (the witnessing fact: `all a: K | committed[a] implies kTransition[a.pre, a.post, …]`).
 * State reads collapse to field access — no folds over the prefix.
 *
 * `Snapshot` is OPAQUE here: a domain extends it with its state record (e.g. InventoryItemState)
 * carrying the payload fields + intra-snapshot invariants as facts on the record sig. CHAINING
 * (one occurrence's `post` is the next one's `pre`, per subject) is deliberately NOT stated here —
 * "the same subject" is a domain notion; each domain pins its chaining fact over its own occurrence
 * kinds, and must pin it UNCONDITIONALLY (a refused action still READ the real prior state; a free
 * `pre` on refused actions lets the solver invent a state that "justifies" any refusal). Snapshot
 * extensionality (identical fields ⇒ identical atom) is likewise the record type's concern
 * (values.als practice). NAMING: `pre`/`post` — `before`/`after` are Alloy 6 temporal KEYWORDS.
 */

open meta/action/action

/** Snapshot — an opaque state record: the value of a subject's mutable payload at one moment.
    Domains extend it with their concrete record type. (The bitemporal version payload is the
    runtime's, RA-02, 2026-11-05; the meta/bitemporal stub left with TN-003 row 3.) */
sig Snapshot {}

/** StatefulAction — an action that carries the snapshots its guards read and its Effect produced. */
abstract sig StatefulAction extends Action {
  pre:  lone Snapshot,   // what the admission guard read (the subject's state just before this tick)
  post: lone Snapshot    // what the Effect produced — iff committed
}

/** A result snapshot exists exactly when the action committed — a refused action produced nothing.
    (`pre` stays `lone` unconstrained here: creation kinds have no prior state to read.) */
fact PostOnlyIfCommitted { all a: StatefulAction | some a.post iff committed[a] }
