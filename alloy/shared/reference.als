module shared/reference

/*
 * Reference — an opaque reference text carried on a record (a customer's order number, a work-order number, the caller's
 * label for a demand's contribution), in its OWN module by the inert-value scope rule (alloy/CLAUDE.md gotcha 7; the
 * shared/note precedent): laws read references only for presence and equality, so Reference atoms are pure solve-time cost
 * to every cone that carries them. Open this ONLY from modules whose records carry references (operations/demand, since
 * TN-004); commands in those cones pin `2 Reference` (1 to exist + 1 to witness a different one).
 *
 * Reflects dafny-domain's `string` fields of the demand (`externalReference`, `referenceOverride`, `sWorkOrder`).
 */

/** Reference — an opaque reference text (content is runtime data); a PURE VALUE with no identity of its own. Unlike a Note,
    its EQUALITY is read: two fields carrying one Reference atom carry the same text (the demand's reference uniqueness
    compares them). SHARED and no-orphan-EXEMPT (the Note precedent — per-consumer orphan facts conflict at the second
    consumer); roots pin scopes instead. */
sig Reference {}
