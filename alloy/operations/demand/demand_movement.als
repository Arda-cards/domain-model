module operations/demand/demand_movement

/*
 * DEMAND — THE POOL MOVEMENT CHAIN (chain B-mov; DT-029 E6, SAMWISE-S1 as ruled 2026-08-28, MINESWEEPER-Q7 = A
 * 2026-09-03). The demand item OWNS a MOVEMENT-semantics intent chain keyed by the INVENTORY POOL a leg mutates:
 * a merge into the holding pool, an extract from it, a transfer to a member pool — each leg is a RESERVE on the
 * pool's chain, the inventory act cites it (`arche` on the pool row — the causal signature of its immediate cause),
 * and the owner CONFIRMs from the citation (`movement/citationView`, adopted); a lost CONFIRM is re-driven from the
 * two heads. Legs cite the demand's own ORIGINATOR row (RecordProduction / ExtractProduction / Distribute) — one leg
 * per pool per originator (DT-029 Q8).
 *
 * CONFINED MODULE (the demand_reset.als precedent, C-2 of the D6 brief): an instance adds seven kinds and a record
 * family to every cone that opens it; the demand unit root is the gate's long pole, so this module is opened ONLY by
 * its dedicated root (tests/unit/demand_movement.als) and by system roots — never by demand_types. The runtime analog
 * holds: the movement saga is a separate service composite (Phase III ships the SEAT — inventory_pool's column,
 * index and citing write path — and NOT this owner chain: SPEARHEAD, 2026-09-03; DT-029 E5 §4).
 */

open operations/demand/demand_implementation                 // the originator kinds + the demand log (real machinery)
open meta/subject_log/subject_log[DemandItem, DemandState] as dlog   // re-opened: aliases do not propagate (I-4)
open meta/intent_log/semantics as sem                        // aliased: pass sem/MoveSem below (the diamond rule)
open meta/intent_log/intent_log[InventoryPool, sem/MoveSem] as movement

// ── the instance: spine + attribution (E2: moved-by-this = a committed pool row cites the leg) ──────────────────
fact MovementSpine       { movement/spineAdopted }
fact MovementAttribution { movement/citationView }   // MOVE chains have no HELD phase: sound + lands is the whole law (E2b)

/** TransferLeg — a leg that moves an item OUT of its key (the source pool) INTO `moveTo` (the destination): the
    inventory `transfer` composite. Keyed on the SOURCE; its two pool rows both carry its arche (Q7 = A). */
sig TransferLeg in movement/ReserveOcc { moveTo: one EntityId }
fact TransferLegTarget { all l: TransferLeg | some p: resolve[l.moveTo] & InventoryPool | p != l.subject }

// ── the owner-side bindings (D6 brief B-1..B-5) ────────────────────────────────────────────────────────────────
fact MovementBindings {
  all o: movement/HolderOcc  | o.holder in DemandItem.eId
  all o: movement/ReserveOcc | o.ownerVersion in dlog/SubjectOcc           // the acting demand version (owner_rid)
  all r: movement/IntentRec  | r.iVersion in dlog/SubjectOcc
  all o: movement/CitingOcc  | o.peerRid in PoolOcc                        // the pool row the act produced
  no movement/ActReserveOcc and no movement/TransferOcc                    // a MOVEMENT instance carries no sub-intents
  all o: movement/HolderOcc | some d: DemandItem | o.holder = d.eId and o.subject.tenantId = d.tenantId   // B-5 tenancy
}
/** LegOrigins — a leg's immediate cause is the demand's own originator row, or itself (a bare leg). One leg per pool per
    originator is a theorem of the module fact `ArcheUnique` on the movement log (DT-029 Q8). */
fact LegOrigins { all o: movement/IntentOcc | o.arche != o implies o.arche in dlog/SubjectOcc }

// ── the peer rows' citation discipline — law A's shape, scoped to THIS chain's citers ────────────────────────────
/** PoolCitations — a pool row that cites one of OUR legs is on that leg's key, or it is the transfer's paired half on
    the destination (Q7 = A). Never "every pool citation is ours": other owners' chains cite pool rows too. */
fact PoolCitations {
  all o: PoolOcc | o.arche in movement/IntentOcc implies
    ( (o.arche & movement/IntentOcc).subject = o.pool
      or (o in PoolAddOcc and some tr: PoolTransferOcc | committed[tr] and tr.to = o.pool and adjacentCommit[tr, o] and tr.arche = o.arche) )
}
/** PoolViews — the RESIDUAL for an additive peer (D-2): an uncited view reads UNMOVED — no ABSENT (pools are minted
    runtime-side; no create kind), no MOVED_OTHERWISE (another owner's movement does not touch this intent). */
fact PoolViews { all o: movement/ViewOcc | not movement/cited[o] implies o.peerView = sem/PV_UNMOVED }

// ── the reads (A-1: the classifier is the module's `citedAt`) and the detector (A-5) ─────────────────────────────
/** movementsCiting — the committed pool rows citing leg `r`. */
fun movementsCiting[r: movement/ReserveOcc]: set PoolOcc { movement/citers[r] & PoolOcc }
/** lateMovement — a committed pool row whose CITED LEG's chain reads FREE at the row's tick (the leg was RELEASEd before
    the act landed — R1 broken by a timeout read as a refusal), AND REMAINS late: a later committed reversal clears it ("later"
    is `ReversalDiscipline`'s `precedes[reversed.tick, o.tick]`, in scope wherever the `q: Pool*Occ` quantifiers are — every cone that
    opens `inventory_pool`), so
    this is a fact about the log as of now, not about the row at its own tick (MINESWEEPER, de9b305 review). The chain read
    is the cited leg's KEY, not the row's own pool: they differ for a transfer's paired add on the destination (PoolCitations'
    second arm), and `phaseAt` reads I_FREE on a pool with no chain — reading `o.pool` reported every such paired add late.
    The `o.arche in movement/IntentOcc` guard excludes UNCITED rows only because `arche` is TOTAL (DT-029 D13 = A): a self-minted row
    has `o.arche = o`, a PoolOcc, so the guard is false. Under a `lone` arche an empty `o.arche` makes `none in IntentOcc` vacuously
    TRUE, `phaseAt[none, t]` reads I_FREE, and this predicate fires on every uncited committed row (MINESWEEPER, 8400902 review). */
pred lateMovement[o: PoolOcc] {
  committed[o] and o.arche in movement/IntentOcc and movement/phaseAt[(o.arche & movement/IntentOcc).subject, o.tick] = sem/I_FREE
  and (no q: PoolAddOcc      | committed[q] and q.reverses = o)   // split per kind: `reverses` is declared on each of the three kinds, so a
  and (no q: PoolRemoveOcc   | committed[q] and q.reverses = o)   //   PoolOcc-typed join is ambiguous (knowledge-base: field-overload; B-mov'' run).
  and (no q: PoolTransferOcc | committed[q] and q.reverses = o)   //   PARENTHESIZED: a quantifier body extends to the end of the formula, so the
}                                                                  //   unparenthesized chain nested the three and never saw a remove (B-mov''' probe)

// ── the laws (L-3 / L-4, the additive form; theorems of `citationView` + the guards) ─────────────────────────────
/** confirmedMovementCited — a committed CONFIRM's leg has a citing pool row (LC-IL-03 read through E2). */
pred confirmedMovementCited { all o: movement/ConfirmOcc | committed[o] implies movement/cited[o] }
/** releasedReserveUncited — a committed RELEASE's leg has no citing pool row before it (LC-IL-04 read through E2). */
pred releasedReserveUncited { all o: movement/ReleaseOcc | committed[o] implies not movement/cited[o] }
/** movementGuarantees — what a consumer may assume of the chain. */
pred movementGuarantees { confirmedMovementCited and releasedReserveUncited }
