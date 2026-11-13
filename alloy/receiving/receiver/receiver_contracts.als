module receiving/receiver/receiver_contracts

/*
 * RECEIVER — CONTRACTS (DT-020/DT-017). The module's laws as NAMED predicates — curated few
 * and strong, each tagged with its consistency class per the kit MATRIX (interaction kind ×
 * module boundary; deployment plays no role):
 *
 *  - Receiver ↔ ReceivingLine ↔ OrderAttribution laws are SAME-MODULE (all three subjects
 *    live here) → ATOMIC invariants. The same-module compositions (line birth + attribution
 *    genesis; the Receive `sActual` fan-out; detach + tombstone) are rendered as PAIRING
 *    ENFORCEMENT FACTS in the implementation and are deliberately NOT in `guarantees`
 *    (the createRecordsAtomically precedent, L9: no mock consumer relies on the pairing,
 *    and publishing it would force attribution machinery into every consumer universe).
 *  - Receiving ↔ resources (item genesis, the pool) and receiving ↔ demand (the distribute
 *    saga closing in `sDeliveries`) are DIFFERENT-MODULE Operations → CONVERGENT/OPERATION
 *    with the CALL-FIRST shape: the caller drives the resources/demand legs FIRST, the
 *    receiving guard is the commit gate. In-flight intermediates are LEGAL (a committed
 *    demand-side PD not yet appended to `sDeliveries` is the ordinary §8.1.3 window; the
 *    PD's reconciliation handle serves orphan recovery — runtime, out of model).
 *  - Receiving never posts to the ORDER: the order's accrual rides the DEMAND edge
 *    (RecordProduction → receiptAccrues, C/NOTIF — the order module's laws; nothing here).
 *
 * THE EXCLUSIVITY LATTICE (§8.5.3): `linePoolExclusiveWhileLive` is this module's lattice
 * row — line pools not shared among lines (own-kind: guard-derived, unconditional) and not
 * held by live cycles or live demand holdings (cross-kind: derived from the guards PLUS the
 * GENESIS PREMISE `receivingPoolGenesis` below — §8.5.3's "guard-and-genesis-derived
 * theorems"). The premise is the model's rendering of the runtime mint discipline (every
 * holder kind mints its pool inside its own act — a fresh mint can never collide with any
 * existing pool); it is a named ASSUMPTION (the groupAxioms/orderAxioms premise mechanism),
 * NEVER a fact — a runtime discipline breach stays representable (premise false), watched
 * by the §8.5.3 integrity monitoring (PDEV-1424), not legislated away.
 */

open receiving/receiver/receiver_types

// ── C1 · the freeze family (§8.2/§8.3) — ATOMIC (same module, all subjects) ─────────────────────
/** Capture-window mutators commit only inside their window: header edits while the Receiver
    is EDITING; line capture edits (expectation cluster + attribution membership) while the
    line is RL_RECEIVING; line genesis while the PARENT receiver is EDITING (same module, the
    guard reads the parent log directly — the frozenOutsideDraft precedent). */
pred captureWindowFrozen {
  all o: receiverHeaderMutators | committed[o] implies rvPre[o].sStatus = RV_EDITING
  all o: lineCaptureMutators    | committed[o] implies rlPre[o].sStatus = RL_RECEIVING
  all o: AddReceivingLineOcc    | committed[o] implies
    receiverStatusAt[parentReceiverOf[o.subject], o.tick] = RV_EDITING
}

// ── C2 · the Complete gate (§8.2) — ATOMIC, the call-first-shaped cascade ───────────────────────
/** A committed Receiver Complete saw NO child line still RL_RECEIVING (the caller's cascade —
    each not-yet-finalized line's Receive — came first; the demand-Complete-settles-members
    shape rendered same-module). Capture ends; distribution may continue. */
pred completeRequiresLinesFinalized {
  all o: CompleteReceiverOcc | committed[o] implies
    (no l: linesOfReceiver[o.subject] | rlStatusAt[l, o.tick] = RL_RECEIVING)
}

// ── C3 · the captured-facts freeze (§8.3.4/§8.3.5) — ATOMIC ─────────────────────────────────────
/** From RL_RECEIVED on, the captured-facts cluster NEVER changes — including the attribution
    MEMBERSHIP (§8.3.3: what freezes is the set; the members' own logs stay live) and the
    birth pins (a freeze boundary is an audit boundary). Post-freeze corrections ride the
    implementation's recorded axis, never a model-level un-freeze (§8.2 reading 2). Only
    `sPool` (detached at release) and `sDeliveries` (append-only) may move. */
pred capturedFactsFrozen {
  all o: rlOccKinds | (committed[o] and some rlPre[o] and rlPre[o].sStatus != RL_RECEIVING) implies {
    rlPost[o].sExpectedItem = rlPre[o].sExpectedItem
    rlPost[o].sExpectedQty  = rlPre[o].sExpectedQty
    rlPost[o].sStatedQty    = rlPre[o].sStatedQty
    rlPost[o].sReceivedQty  = rlPre[o].sReceivedQty
    rlPost[o].sRejectedQty  = rlPre[o].sRejectedQty
    rlPost[o].sOffManifest  = rlPre[o].sOffManifest
    rlPost[o].sRejectionReason = rlPre[o].sRejectionReason   // DT-022 TQ-2 (cut 6)
    rlPost[o].sNote         = rlPre[o].sNote                  // DT-022 TQ-2 (cut 6)
    rlPost[o].sBirthPins    = rlPre[o].sBirthPins
    rlPost[o].sAttributions = rlPre[o].sAttributions
  }
}

// ── C4 · the same-Item pool gate (§8.3/§8.3.2) — CONVERGENT/OPERATION gate, receiving-side ──────
/** A committed Receive that attached a pool saw the expected item RESOLVED (§8.3.2: no later
    than Receive) and the pool denominated in it (the RPoolWrongItem/sight-of-card precedent).
    Both compared fields are immutable identity-structure, so the gate cannot go stale. */
pred receiveSameItemPool {
  all o: ReceiveLineOcc | (committed[o] and some o.pool) implies {
    some rlPre[o].sExpectedItem
    (resolve[o.pool] & InventoryPool).itemPin.subject = rlPre[o].sExpectedItem.subject
  }
}

// ── C5 · the Σ-invariants (§8.3.3 d) — ATOMIC, case-wise ────────────────────────────────────────
/** A committed Receive's allocation drew only on the frozen-at-this-instant membership and
    never over-allocated: keys ⊆ the pre membership, and (CASE-WISE, ≤2 keys — the
    order_received solver ceiling, documented in the implementation) Σ allocation ≤ the
    accepted count. The attach-side twin (Σ expected ≤ sExpectedQty) is guard-enforced the
    same way; its law is subsumed by the guards and witnessed in the suite (refusal runs). */
pred receiveAllocationBounded {
  all o: ReceiveLineOcc | committed[o] implies {
    o.allocation.Quantity in rlPre[o].sAttributions
    (#(o.allocation.Quantity) = 1 implies
      (all k: o.allocation.Quantity |
        lte[qtyMap[k.(o.allocation)], qtyMap[o.receivedQty]]))
    (#(o.allocation.Quantity) = 2 implies
      (all disj k1, k2: o.allocation.Quantity |
        lte[add[qtyMap[k1.(o.allocation)], qtyMap[k2.(o.allocation)]], qtyMap[o.receivedQty]]))
  }
}

// ── C6 · the actual facet is set-once (§8.3.3 b) — ATOMIC ───────────────────────────────────────
/** Once present, `sActual` never changes; and it becomes present only through a committed
    RecordActual (which the implementation pairs with the line's Receive — the fan-out). */
pred actualSetOnce {
  all o: oaOccKinds | (committed[o] and some oaPre[o].sActual) implies
    oaPost[o].sActual = oaPre[o].sActual
  all a: OrderAttribution, t: Tick | some oaStateAt[a, t].sActual implies
    (some x: RecordActualOcc | committed[x] and x.subject = a and notAfter[x.tick, t])
}

// ── C7 · deliveries append-only (§8.1.3 P2) — ATOMIC (the line's own field) ─────────────────────
/** `sDeliveries` never shrinks: the owner-carried distribution ledger only accumulates
    (reversals are the PD's OWN terminal Revoke — reversing-entry semantics; the fold reads
    delivery status, never membership removal). */
pred deliveriesAppendOnly {
  all o: rlOccKinds | committed[o] implies rlPre[o].sDeliveries in rlPost[o].sDeliveries
}

// ── C8 · forward monotonicity + terminal closure (SL-4 family) — ATOMIC ─────────────────────────
/** The line's three-state machine never regresses (RECEIVING → RECEIVED → DISTRIBUTED). */
pred lineForwardMonotone {
  all l: ReceivingLine, t1, t2: Tick | notAfter[t1, t2] implies {
    rlStatusAt[l, t1] = RL_RECEIVED implies rlStatusAt[l, t2] in RL_RECEIVED + RL_DISTRIBUTED
    rlStatusAt[l, t1] = RL_DISTRIBUTED implies rlStatusAt[l, t2] = RL_DISTRIBUTED
  }
}
/** Once COMPLETE, the Receiver's CAPTURE record never changes again (capture is over; there
    is no reopen — post-freeze corrections are recorded-axis territory). Field-wise since
    cut 6: `sInternalNotes` is the ONE deliberate exemption (DT-022 TQ-7(c) — internal notes
    are editable at any time; their history rides the log). */
pred receiverTerminalComplete {
  all r: Receiver, t1, t2: Tick |
    (notAfter[t1, t2] and receiverStatusAt[r, t1] = RV_COMPLETE) implies {
      receiverStateAt[r, t2].sStatus       = receiverStateAt[r, t1].sStatus
      receiverStateAt[r, t2].sBillOfLading = receiverStateAt[r, t1].sBillOfLading
      receiverStateAt[r, t2].sCarrierPin   = receiverStateAt[r, t1].sCarrierPin
      receiverStateAt[r, t2].sCarrierRole  = receiverStateAt[r, t1].sCarrierRole
      receiverStateAt[r, t2].sOperator     = receiverStateAt[r, t1].sOperator
    }
}

// ── C9 · the exclusivity-lattice row (§8.5.3) — checks-not-facts, guard-and-genesis-derived ─────
/** receivingPoolGenesis — THE GENESIS PREMISE (assume when: pools are minted inside their
    holder's own attach act — the §8.5.3 ownership-by-genesis runtime discipline; PDEV-1424
    monitors it). Model rendering: no pool is named by two committed pool-attaching acts
    across the kinds visible to this module (cycle StartProcessing, demand StartProduction
    and — since TN-004 — the demand's EXTERNAL ATTACHES, the line's Receive). A NAMED PREMISE,
    never a fact — a discipline breach stays representable, and a weakened guard stays
    refusable (the R1 distinction). TEN clauses since DT-016 PR B (dafny-domain
    `ReceivingPoolGenesis` with `ExternalAttachGenesis`, MD-087): the last four are the external
    attach against itself and against each of the three other kinds. */
pred receivingPoolGenesis {
  all disj a, b: StartProcessingOcc | (committed[a] and committed[b]) implies no (a.pool & b.pool)
  all disj a, b: StartProductionOcc | (committed[a] and committed[b]) implies no (a.holding & b.holding)
  all disj a, b: ReceiveLineOcc         | (committed[a] and committed[b]) implies no (a.pool & b.pool)
  all a: StartProcessingOcc, b: StartProductionOcc |
    (committed[a] and committed[b]) implies no (a.pool & b.holding)
  all a: ReceiveLineOcc, b: StartProcessingOcc |
    (committed[a] and committed[b]) implies no (a.pool & b.pool)
  all a: ReceiveLineOcc, b: StartProductionOcc |
    (committed[a] and committed[b]) implies no (a.pool & b.holding)
  // the external attach's four (dafny-domain `ExternalAttachGenesis`)
  all disj a, b: AttachOcc |
    (committed[a] and committed[b] and (a.contribution + b.contribution) in ExternalContribution)
      implies no (a.contribution.cPool & b.contribution.cPool)
  all a: StartProcessingOcc, b: AttachOcc |
    (committed[a] and committed[b] and b.contribution in ExternalContribution) implies no (a.pool & b.contribution.cPool)
  all a: StartProductionOcc, b: AttachOcc |
    (committed[a] and committed[b] and b.contribution in ExternalContribution) implies no (a.holding & b.contribution.cPool)
  all a: ReceiveLineOcc, b: AttachOcc |
    (committed[a] and committed[b] and b.contribution in ExternalContribution) implies no (a.pool & b.contribution.cPool)
}
/** linePoolProvenance — a line-held pool is EXACTLY the pool its committed Receive named
    (the receiver-side mirror of kanban's `poolProvenance` and demand's `holdingProvenance`
    — the §8.5.3 symmetric publication). A theorem of the Receive effect + the frozen
    frames (Receive is the only `sPool` setter and names its own payload; every other kind
    carries or clears); holds for terminal records too. Published 2026-08-24: DT-024 E7
    proved it the load-bearing conjunct of the lattice row's inductive invariant. */
pred linePoolProvenance {
  all l: ReceivingLine, t: Tick | some rlStateAt[l, t].sPool implies
    (some o: ReceiveLineOcc | committed[o] and o.subject = l and notAfter[o.tick, t]
       and rlStateAt[l, t].sPool = o.pool)
}
/** linePoolExclusiveWhileLive — the receiving LATTICE ROW (§8.5.3): time-indexed over live
    holders, a line pool is (i) held by at most one line — OWN-KIND, unconditional, derived
    from the Receive guard's availability clause + the frozen frames; and (ii) under the
    genesis premise, never simultaneously a live cycle's pool or a live demand's holding —
    CROSS-KIND, the layers receiving can see (kanban's own row is `poolExclusiveWhileLive`;
    demand's is `holdingExclusiveWhileLive`; the global row is dafny-domain's
    `PoolLattice.PoolLatticeGlobal`, and the system tier keeps its finders, QA761).
    UNIT-tier dischargeable since cut 5: the peers publish their pool-provenance
    laws (`poolProvenance`/`holdingProvenance`), tying mock record bindings to attach
    payloads. Joined `guarantees` in the same change set as its first discharge (the
    §8.5.3 mock rule). */
// DT-023 cut 8, the D-1b decomposition (soak-verification-specification): the row is
// EXACTLY the conjunction of three facets, each gate-checkable in a universe that
// excludes the other holder kinds — gate-tier assurance while the full conjunction's
// UNSAT proof runs at the soak tier (soak_rcv_linePoolExclusiveUnitScope). The
// decomposition is exact (conjunction ≡ the row), so no assume-guarantee argument is
// needed beyond the facets themselves.
/** linesPoolLoneHolder — facet (i), OWN-KIND, unconditional: at any tick a pool is held
    by at most one line. */
pred linesPoolLoneHolder {
  all t: Tick, p: InventoryPool |
    lone { l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p }
}
/** lineCyclePoolDisjoint — facet (ii)/cycles, under the genesis premise: a line-held pool
    is never simultaneously a live cycle's pool. */
pred lineCyclePoolDisjoint {
  receivingPoolGenesis implies
    all t: Tick, p: InventoryPool |
      (some l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p) implies
        (no c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p)
}
/** lineDemandPoolDisjoint — facet (ii)/demands, under the genesis premise: a line-held
    pool is never simultaneously a live demand's holding. */
pred lineDemandPoolDisjoint {
  receivingPoolGenesis implies
    all t: Tick, p: InventoryPool |
      (some l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p) implies
        (no d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p)
}
pred linePoolExclusiveWhileLive {
  linesPoolLoneHolder and lineCyclePoolDisjoint and lineDemandPoolDisjoint
}
/** lineContributionPoolDisjoint — the row against the FOURTH holder kind (TN-004; dafny-domain
    `LineContributionPoolDisjoint`, MD-087), under the genesis premise (its Receive-against-attach clause): a line-held
    pool is never simultaneously the pool of a live demand's external contribution. Its OWN published law, beside the
    row and not a conjunct of it: `linePoolExclusiveWhileLive` keeps the three-facet statement the E7 inductive root
    (advanced/receiver_pool_inductive.als) proves slice-faithful. Reads `linePoolProvenance` and the demand's
    `contributionFrom`. */
pred lineContributionPoolDisjoint {
  receivingPoolGenesis implies
    all t: Tick, p: InventoryPool |
      (some l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p) implies
        (no d: DemandItem, c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p)
}

// ── the promise ─────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws. (The
    same-module pairing compositions are deliberately NOT here — see the header; the genesis
    premise is an assumption, not a promise, and rides INSIDE the lattice row's conditional.) */
pred guarantees {
  captureWindowFrozen
  and completeRequiresLinesFinalized
  and capturedFactsFrozen
  and receiveSameItemPool
  and receiveAllocationBounded
  and actualSetOnce
  and deliveriesAppendOnly
  and lineForwardMonotone
  and receiverTerminalComplete
  and linePoolProvenance
  and linePoolExclusiveWhileLive
  and lineContributionPoolDisjoint   // the row against the fourth holder (TN-004, MD-087); Dafny LineContributionPoolDisjoint
}
