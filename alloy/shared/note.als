module shared/note

/*
 * Note — the record-carried annotation value, in its OWN module by the inert-value scope
 * rule (MP ruling, 2026-08-10; CLAUDE.md gotcha 7): laws read notes only for
 * presence/equality, so Note atoms are pure solve-time cost to every cone that carries
 * them — a seat in `shared/values` (every domain cone) made ~40 unrelated roots pay
 * default-scope Note atoms. Open this ONLY from modules whose records carry notes
 * (order, receiver, kanban_card); commands in those cones pin `2 Note` (1 to exist + 1 to witness
 * replace-with-different — add/remove/replace is all a counterexample can do).
 *
 * The OCCURRENCE-level note is NOT a Note: it is the inert `note: lone String` on the
 * core `Occurrence` (`meta/occurrence` — zero atoms in commands without literals).
 */

/** Note — an opaque free-text annotation (content is runtime data); a PURE VALUE with no
    identity of its own (the Quantity posture — DT-022 TQ-7(c), MP ruling 2026-08-08).
    Entities adopt it by carrying `lone Note` / `set Note` fields; an entity may carry one
    or MULTIPLE notes, and future note KINDS remain per-adopter extensions. Atoms are
    NOMINAL: two Note atoms may carry the same runtime text, so there is deliberately no
    extensional fact. SHARED and no-orphan-EXEMPT (the SupplierReference / DT-004 Q8
    precedent for shared value sigs — per-consumer orphan facts conflict at the second
    consumer); roots pin scopes instead. */
sig Note {}
