module operations/demand/demand_implementation

/*
 * DEMAND — IMPLEMENTATION (DT-016/DT-017). The log machinery: spine adoption, reason-precise
 * admission guards, and per-kind effects (record frames). The demand ↔ kanban interactions are
 * CONVERGENT/OPERATION with the CALL-FIRST saga shape (see demand_contracts.als): there is NO
 * cross-log enforcement fact — the demand guards ARE the saga commit gates, reading the member
 * cycles' current states; in-flight intermediates are legal. Integration roots open this file
 * to get the REAL module.
 *
 * GUARDS READ `o.pre` (the chained record — the state the operation actually saw; refusals
 * included). Cycle-side reads at `o.tick` are STRICTLY-BEFORE state: OneOccurrencePerTick means
 * `o` itself occupies the tick.
 *
 * CONTRIBUTIONS (TN-004; reflects dafny-domain src/operations/demand/demand.dfy at 0040544, arm for arm): the demand's
 * quantity is no longer stored. It is a READ, the keyed sum of the live contributions, CONFINED to demand_quantity.als
 * (opened ONLY by its dedicated root: the demand cone cannot carry the general keyed fold). Nothing here reads it.
 */

open operations/demand/demand_contracts
open operations/demand/demand_types as dt   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[dt/DemandItem, dt/DemandState] as dlog   // same params ⇒ the SAME spine instance as demand_types
open meta/subject_log/lifecycle[dt/DemandItem, dt/DemandState] as lc       // same params ⇒ the SAME shapes instance
open meta/subject_log/subject_log[dt/ProductionDelivery, dt/PDState] as pdlog  // the second subject's spine (§8.1.2)
open meta/subject_log/lifecycle[dt/ProductionDelivery, dt/PDState] as pdlc     // same params ⇒ the SAME shapes instance (cut 2)
open meta/activation/activation   // the activation every row cites (DT-015 D1 to D3)

// ── spine adoption (DT-015 Q5; the PD spine §8.1.2) ─────────────────────────────────────────────
fact DemandChaining      { dlog/chained }
fact PDChaining          { pdlog/chained }
one sig DemandService extends Service {}   // DT-015 R2: the service's activation log, adopted beside the spine
fact DemandActivated      { activated[DemandService, dlog/SubjectOcc] }
fact PDActivated          { activated[DemandService, pdlog/SubjectOcc] }

// ── the §8.1.2 ATOMIC compositions (enforcement facts — the model's rendering of the ONE
// demand tx; see the C8 contracts note for why these are facts here and not in `guarantees`) ──
fact CreateComposesWithRecord  { createRecordsAtomically }
fact RevokeComposesWithExtract { revokeExtractsAtomically }

// ── guard-side reads ────────────────────────────────────────────────────────────────────────────
/** liveAtOccD — the demand item is STARTED, not retired (the lifecycle module's shape half) and in a LIVE status
    (the domain half) as the operation reads it (pre-record). The former started/deleted-before preds are the
    module's `lc/startedBefore` / `lc/retiredBefore` since 2026-09-09. */
pred liveAtOccD[o: dlog/SubjectOcc] { lc/liveAt[o] and dPre[o].sStatus in liveStatuses }
// (preMemberCycles / preLiveContributionIds live in demand_types — the contracts' commit-gate laws
// read them too.)

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ───────────────────
/** createGenesisViol — the genesis conditions shared by both create kinds. (NO uniqueness check —
    R1 amended: multiple DemandItems per (Item, Source Station) are legal; single-OPEN, if a
    deployment wants it, is CALLER policy over the `demandsFor` read.) */
fun createGenesisViol[o: lc/CreateOcc]: set Reason {
  lc/createViol[o, RDemandStarted]
  // (No item/station tenancy clause: stationRef is an ENTITY dataRef — kernel isolation makes a
  //  cross-tenant resolution UNREPRESENTABLE; the itemPin's tenancy is the DemandItemPinTenancy
  //  fact (DT-023 — same unrepresentable posture). RForeignRef remains for the RECORD-carried
  //  refs: holding, delivery.)
  // (The retirement clause moved to createViol at DT-023 cut 8 — see there.)
}
// DT-023 cut 7a: a committed genesis pins the item's CURRENT version at its tick (Q-A currency).
fact DemandItemPinCurrency {
  all o: CreateDemandOcc + CreateWithContributionOcc | committed[o] implies
    pinsCurrentItem[o.subject.itemPin, o.tick]
}
/** attachCycleViol — the SAGA COMMIT GATE for attach (C/OP call-first): the member must be an
    in-tenant, live cycle standing at REQUESTED (its Accept — the saga's first leg — already
    committed) and held by no live demand. Conservative refusal on a dangling ref. NB the held
    check excludes `o.subject`: a demand read at `o.tick` would see o's OWN commit (LOCF reads
    are inclusive) and refuse itself; OTHER demands' reads at `o.tick` are strictly-before by
    OneOccurrencePerTick. Already-a-member-of-THIS-demand is the separate pre-side check. */
fun attachCycleViol[o: dlog/SubjectOcc, m: EntityId]: set Reason {
  (let c = resolve[m] & CardCycle |
    ((some c and c.tenantId != o.subject.tenantId) => RForeignCycle else none)
    + ((no c or not liveCycleAt[c, o.tick] or statusAt[c, o.tick] != REQUESTED)
       => RCycleIneligible else none)
    + ((some c and some d2: DemandItem - o.subject | liveDemandAt[d2, o.tick] and c in attachedAt[d2, o.tick])
       => RCycleHeld else none)
    + ((some c: dPre[o].sContributions & CardContribution | c.cycleRef = m) => RCycleHeld else none))
}
// DT-023 cut 8 (gate at INCEPTION, never at PROPAGATION — MP ruling 2026-08-11): the
// retirement gate binds ONLY on the DIRECT create (the caller chooses the item — F6
// card-less demand, queue-add of a new item). The WITH-CYCLE create is PROPAGATION —
// its pin is inherited from the triggering cycle, whose REQUEST was the gated
// inception — and refusing it would strand the scan workflow.
fun createViol[o: CreateDemandOcc]: set Reason {
  createGenesisViol[o]
  + ((not itemLiveAt[o.subject.itemPin.subject, o.tick]) => RRetiredRef else none)
}
/** contributionIdentityViol — the attach's identity arms (dafny-domain IdentityViol). The id is used ONCE per demand: a committed attach
    of this demand already carried it (a removed id included — the arm reads the log, not the state). And the reference, AS
    READ (`referenceOf`: a card's default is its card's serial), is carried by no contribution the demand holds — a withdrawn
    card's entry included, until its DetachWithdrawn. */
fun contributionIdentityViol[o: AttachOcc]: set Reason {
  ((some a: AttachOcc - o | committed[a] and a.subject = o.subject and precedes[a.tick, o.tick]
       and a.contribution.cid = o.contribution.cid)
     => RContributionStarted else none)
  + ((some referenceOf[o.contribution] and some c: dPre[o].sContributions | referenceOf[c] = referenceOf[o.contribution])
     => RDuplicateReference else none)
}
/** poolUsedBefore — the pool was already USED before `o` (dafny-domain `KC.PoolUsed` or `PoolUsedByDemands`): the resolved
    pool has committed MEMBERSHIP history (its genesis row is its minting, not a use), or a committed StartProcessing named
    the id, or a committed external attach — of ANY demand — named it (`PoolUsedByContribution`), or a committed
    StartProduction — of ANY demand — named it as its holding (`PoolUsedByHolding`, MD-083). ONE notion of a used pool,
    read by the external attach and by StartProduction alike; a Complete or a Cancel does not erase it (released at rest
    is not fresh). MEMBERSHIP rows are the pool's three Mutate kinds (dafny-domain `ShapeOf == Mutate`), as the kanban's
    freshness arm reads them: an affirmation writes nothing and is no use (witness `unit_dem_affirmedPoolStaysFresh`). */
pred poolUsedBefore[id: EntityId, o: Occurrence] {
  (some p: resolve[id] & InventoryPool, b: PoolAddOcc + PoolRemoveOcc + PoolTransferOcc |
     committed[b] and b.subject = p and precedes[b.tick, o.tick])
  or (some sp: StartProcessingOcc | committed[sp] and sp.pool = id and precedes[sp.tick, o.tick])
  or (some a: AttachOcc - o | committed[a] and precedes[a.tick, o.tick]
        and a.contribution in ExternalContribution and a.contribution.cPool = id)
  or (some sp: StartProductionOcc - o | committed[sp] and precedes[sp.tick, o.tick] and sp.holding = id)
}
/** externalPoolViol — the external contribution's pool arms (dafny-domain ExternalPoolViol): the pool exists and is live,
    is in the demand's tenant, carries the demand's item, and is FRESH. */
fun externalPoolViol[o: AttachOcc, e: ExternalContribution]: set Reason {
  ((not namedPoolLive[e.cPool, o.tick]) => RNoSuchPool else none)
  + ((some p: resolve[e.cPool] & InventoryPool | p.tenantId != o.subject.tenantId) => RForeignRef else none)
  + ((some p: resolve[e.cPool] & InventoryPool | p.itemPin.subject != o.subject.itemPin.subject) => RWrongItem else none)
  + (poolUsedBefore[e.cPool, o] => RPoolNotFresh else none)
}
/** contributionViol — the arms of the contribution's KIND: a card's saga gate, an external one's pool arms. */
fun contributionViol[o: AttachOcc]: set Reason {
  ((o.contribution in CardContribution) => attachCycleViol[o, o.contribution.cycleRef] else none)
  + ((o.contribution in ExternalContribution) => externalPoolViol[o, o.contribution] else none)
}
// The retirement gate binds at INCEPTION (DT-023 cut 8): on the direct create, and on a genesis with an EXTERNAL
// contribution (the caller chooses the item). A genesis with a CARD contribution is PROPAGATION — its item was gated at the
// cycle's REQUEST — and refusing it would strand the scan workflow.
fun createWithViol[o: CreateWithContributionOcc]: set Reason {
  createGenesisViol[o]
  + ((o.contribution in ExternalContribution and not itemLiveAt[o.subject.itemPin.subject, o.tick]) => RRetiredRef else none)
  + contributionIdentityViol[o] + contributionViol[o]
}
fun addViol[o: AddContributionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + contributionIdentityViol[o] + contributionViol[o]
}
/** notContributionViol — the id names no contribution the demand holds (as the operation reads it). */
fun notContributionViol[o: TargetOcc]: set Reason {
  (o.target not in dPre[o].sContributions.cid) => RNotContribution else none
}
fun removeViol[o: RemoveContributionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + notContributionViol[o]
  + ((some c: dPre[o].sContributions & CardContribution | c.cid = o.target
        and no k: cyclesOf[c] | liveCycleAt[k, o.tick] and statusAt[k, o.tick] = REQUESTING)
     => RCycleIneligible else none)   // C/OP gate: the card's Shelve (the saga's first leg) already committed
  + ((some e: dPre[o].sContributions & ExternalContribution | e.cid = o.target
        and some p: resolve[e.cPool] & InventoryPool | some heldAt[p, o.tick])
     => RPoolNotEmpty else none)      // an external contribution leaves only while its pool is empty
}
fun editViol[o: EditContributionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + notContributionViol[o]
  + ((some o.newQuantity and some c: dPre[o].sContributions & CardContribution | c.cid = o.target)
     => RNotExternal else none)       // a card contribution's quantity is its cycle's
  + ((some o.newReference and o.target in dPre[o].sContributions.cid
        and some c: dPre[o].sContributions | c.cid != o.target and referenceOf[c] = o.newReference)
     => RDuplicateReference else none)
}
/** contributionNotesViol — NOT under the freeze: admitted while the demand has history and no tombstone (any status). */
fun contributionNotesViol[o: SetContributionNotesOcc]: set Reason {
  ((not lc/liveAt[o]) => RDemandClosed else none) + notContributionViol[o]
}
fun userNotesViol[o: SetUserNotesOcc]: set Reason {
  (not lc/liveAt[o]) => RDemandClosed else none
}
fun workOrderViol[o: SetWorkOrderOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RBadState else none)
}
fun fulfillmentNotesViol[o: SetFulfillmentNotesOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus not in (DS_OPEN + DS_RELEASED)) => RBadState else none)
}
fun detachWithdrawnViol[o: DetachWithdrawnOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + notContributionViol[o]
  + ((some c: dPre[o].sContributions & CardContribution | c.cid = o.target and some k: cyclesOf[c] | liveCycleAt[k, o.tick])
     => RCycleLive else none)
  + ((some e: dPre[o].sContributions & ExternalContribution | e.cid = o.target) => RNotContribution else none)   // a detach reconciles a CARD
}
fun releaseViol[o: ReleaseOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RBadState else none)
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_OPEN and no liveContributionsOf[dPre[o].sContributions, o.tick])
     => RNoContribution else none)   // TN-004: nothing to produce for
}
fun reopenViol[o: ReopenOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_RELEASED) => RBadState else none)
}
fun startProductionViol[o: StartProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_RELEASED) => RBadState else none)
  + ((some p: resolve[o.holding] & InventoryPool | p.tenantId != o.subject.tenantId)
     => RForeignRef else none)
  + ((some p: resolve[o.holding] & InventoryPool | p.itemPin.subject != o.subject.itemPin.subject)
     => RWrongItem else none)   // QA704 Q4 (a), DT-009 Q27: M3.2 as the arm it is in dafny-domain StartProductionViol (was the fact StartProductionHoldingPoolPin)
  + ((some o.holding and not namedPoolLive[o.holding, o.tick]) => RNoSuchPool else none)   // QA704 Q2 (b), MD-074: the holding must exist and be live
  + ((some o.holding and poolUsedBefore[o.holding, o]) => RPoolNotFresh else none)          // TN-004 row 17, MD-083: the holding must be FRESH
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_RELEASED
      and some c: preMemberCycles[o] | statusAt[c, o.tick] != IN_PROCESS)
     => RCycleIneligible else none)   // C/OP gate: every live member's StartProcessing (saga's first legs) already committed
}
fun recordProductionViol[o: RecordProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((liveAtOccD[o] and some dPre[o].sHolding and not namedPoolLive[dPre[o].sHolding, o.tick]) => RNoSuchPool else none)   // QA704 Q2 (b): the holding may retire between two deliveries; the genesis refuses the same (one verdict)
  + ((some pd: resolve[o.delivery] & ProductionDelivery | pd.tenantId != o.subject.tenantId)
     => RForeignRef else none)   // §8.1.2: delivery now = the PD entity, not the transient pool
  // M3 (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): pool-vs-demand item agreement — the act binds the
  // delivery pool's PIN, not a caller-carried item (SPEARHEAD brief item R2). RecordProduction
  // carries no pool field of its own (compose-don't-subsume: the paired CreateDeliveryOcc
  // asserts it — the same asymmetric shape the Revoke/Extract pair already uses, neither side
  // duplicating the other's fields); this reads the pool through the §8.1.2 ATOMIC pairing
  // (`createRecordsAtomically`) — the COMMITTED CreateDeliveryOcc naming the SAME
  // ProductionDelivery for the SAME demand. MF-003 (MP, 2026-10-16) REVERSES the earlier clause
  // "independent of that CreateDeliveryOcc's OWN admission (a candidate `c` need not itself be
  // committed)": read over every create, a REFUSED wrong-pool create stayed in the arm's range,
  // so the honest retry's record (same delivery id, a pool that agrees) was refused RWrongItem,
  // and `createRecordsAtomically` then excluded the retry instead of letting it commit. Over
  // committed creates the arm is subsumed in this universe by the create-side arm (ids are keys,
  // pins static); it stays for the runtime, where the pools can change between the two halves.
  + ((some c: CreateDeliveryOcc, p: resolve[c.pool] & InventoryPool |
        committed[c] and c.subject.eId = o.delivery and c.subject.demandRef = o.subject.eId
        and p.itemPin.subject != o.subject.itemPin.subject)
     => RWrongItem else none)
}
fun extractProductionViol[o: ExtractProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((some pd: resolve[o.delivery] & ProductionDelivery | pd.tenantId != o.subject.tenantId)
     => RForeignRef else none)
}
// ── the PD subject's guards (§8.1.2/§8.1.4) ────────────────────────────────────────────────────
// startedBeforePD retired at cut 2: the family's `pdlc/startedBefore` is the same reading, declared once.
/** createDeliveryViol — the §8.1.4 target gates. The demandRef is an ENTITY dataRef: kernel
    isolation makes a cross-tenant resolution UNREPRESENTABLE (the entity-lift precedent), so
    there is no tenancy clause; a DANGLING or non-IN_PROCESS target refuses conservatively via
    the status read. Both clauses may fire together (reason-precise = the SET). */
fun createDeliveryViol[o: CreateDeliveryOcc]: set Reason {
  pdlc/createViol[o, RDeliveryStarted]                       // genesis-once — the family's arm (cut 2)
  + ((some d: resolve[o.subject.demandRef] & DemandItem | some demandStateAt[d, o.tick].sHolding
        and not namedPoolLive[demandStateAt[d, o.tick].sHolding, o.tick]) => RNoSuchPool else none)   // QA704 Q2 (b), reading A: the pair keeps one verdict
  + ((demandStatusAt[resolve[o.subject.demandRef] & DemandItem, o.tick] != DS_IN_PROCESS)
     => RTargetNotInProcess else none)
  // M3 (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): re-based from a caller-asserted item to the
  // DELIVERY POOL's pin — §8.1.4 item agreement, the pool module's reason REUSED. Silent
  // (no violation) when `o.pool` doesn't resolve to an InventoryPool — a dangling/unset pool
  // ref is not this guard's concern (mirrors the RForeignRef pattern elsewhere in this file).
  + ((some p: resolve[o.pool] & InventoryPool | p.itemPin.subject != (resolve[o.subject.demandRef] & DemandItem).itemPin.subject)
     => RWrongItem else none)
}
/** revokeDeliveryViol — §8.1.1: subject live + DI live. The content clause (holding content ≥
    contributed) is RUNTIME enforcement + probe — the standing I3 arity-4 exclusion; the
    caller's own source-state check (RL allows) is the CALLER's leg, ordinary call-first. */
fun revokeDeliveryViol[o: RevokeDeliveryOcc]: set Reason {
  pdlc/liveViol[o, RDeliveryClosed]                          // never created / already RETIRED — the family's arm (cut 2)
  + ((pdlc/liveAt[o] and pdPre[o].sStatus = PD_REVOKED) => RDeliveryClosed else none)   // already revoked — the domain's arm, same atom
  + ((let d = resolve[o.subject.demandRef] & DemandItem | no d or not liveDemandAt[d, o.tick])
     => RDemandClosed else none)
}
/** retireDeliveryViol — cut 2 (Q24 (a)): the family's arm (never created / already retired → RDeliveryClosed) + the
    domain's terminality arm: a delivery still CREATED is not terminal — Revoke first (RNotTerminal, the demand's atom). */
fun retireDeliveryViol[o: RetireDeliveryOcc]: set Reason {
  pdlc/retireViol[o, RDeliveryClosed]
  + ((pdlc/liveAt[o] and pdPre[o].sStatus = PD_CREATED) => RNotTerminal else none)
}
fun distributeViol[o: DistributeOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((liveAtOccD[o] and (o.allocation.Quantity + o.fills) not in preLiveContributionIds[o])
     => RBadAllocation else none)     // a key or a fill that is no LIVE contribution: a withdrawn card receives NOTHING (R7/R8)
  + ((liveAtOccD[o] and some c: dPre[o].sContributions & CardContribution | c.cid in o.fills
        and some k: cyclesOf[c] | statusAt[k, o.tick] != READY)
     => RCycleIneligible else none)   // C/OP gate: each CARD fill's CompleteProcessing already committed; an external fill has no cycle to gate
}
/** badPlacement — the placements name a pool the demand does not release (`PlacePerPool`), an item no released pool holds,
    or an item in two locators' sets (`PlacePerItem`). `PlaceAll` never does. (dafny-domain `BadPlacement`.) */
pred badPlacement[o: CompleteOcc] {
  let pp = (o.placements & PlacePerPool).byPool, pi = (o.placements & PlacePerItem).byLocator | {
    (some e: pp.PhysicalLocator | e not in releasedPoolIds[dPre[o]])
    or (some i: PhysicalLocator.pi | i not in (EntityId.(heldByReleased[o])).eId)
    or (some i: EntityId, disj l1, l2: PhysicalLocator | i in l1.pi and i in l2.pi)
  }
}
/** completeViol — arm for arm from dafny-domain `CompleteViol` (DT-016 PR B): the retired-holding arm and its reason
    RUndistributed LEFT (TN-004 row 11, MD-084); the three placement arms read the pairs (released pool, item it holds) as
    this Complete reads them — call-first, the items were moved before. */
fun completeViol[o: CompleteOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((liveAtOccD[o] and some p: resolve[dPre[o].sHolding] & InventoryPool, w: lastPoolWrite[p, o.tick] | not atOrBefore[w.at, o.at])
     => RBackdatedHolding else none)   // COORDINATOR-Q527 A5: the holding's newest write dated after this commit's own stamp
  + ((liveAtOccD[o] and some c: preMemberCycles[o] | statusAt[c, o.tick] = IN_PROCESS)
     => RCycleIneligible else none)   // C/OP gate: every member SETTLED first (READY or back to REQUESTING)
  + ((liveAtOccD[o] and badPlacement[o]) => RBadPlacement else none)                       // TN-004 row 13
  + ((liveAtOccD[o] and some e: EntityId, x: InventoryItem |
        e -> x in heldByReleased[o] and no placedLocator[o.placements, e, x])
     => RPlacementIncomplete else none)                                                    // row 13: every held item has a locator
  + ((liveAtOccD[o] and some e: EntityId, x: InventoryItem |
        e -> x in heldByReleased[o] and some placedLocator[o.placements, e, x]
        and stateAt[x, o.tick].sLocator != placedLocator[o.placements, e, x])
     => RUnplaced else none)                                                               // row 14: … and already sits there (the inventory-item log's read)
}
fun cancelViol[o: CancelOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RBadState else none)
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_OPEN and some dPre[o].sContributions & CardContribution) => RHasCards else none)
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_OPEN
      and some e: dPre[o].sContributions & ExternalContribution, p: resolve[e.cPool] & InventoryPool | some heldAt[p, o.tick])
     => RPoolNotEmpty else none)   // QA739 (a), MD-085: no external pool's content goes to rest without a placement
}
fun deleteViol[o: DeleteDemandOcc]: set Reason {
  lc/retireViol[o, RDemandClosed]                                                      // not started, or already retired
  + ((lc/startedBefore[o] and dPre[o].sStatus in liveStatuses) => RNotTerminal else none)   // delete requires a TERMINAL demand
}
/** demandDomainViol — the witness BY SHAPE (the lifecycle idiom): one dispatch over the Mutate kinds; each kind's
    own violation set (its liveness arm included) is unchanged. */
fun demandDomainViol[o: lc/MutateOcc]: set Reason {
  (o in AddContributionOcc => addViol[o] else none) + (o in RemoveContributionOcc => removeViol[o] else none)
  + (o in EditContributionOcc => editViol[o] else none) + (o in SetContributionNotesOcc => contributionNotesViol[o] else none)
  + (o in SetUserNotesOcc => userNotesViol[o] else none) + (o in SetWorkOrderOcc => workOrderViol[o] else none)
  + (o in SetFulfillmentNotesOcc => fulfillmentNotesViol[o] else none)
  + (o in DetachWithdrawnOcc => detachWithdrawnViol[o] else none) + (o in ReleaseOcc => releaseViol[o] else none)
  + (o in ReopenOcc => reopenViol[o] else none) + (o in StartProductionOcc => startProductionViol[o] else none)
  + (o in RecordProductionOcc => recordProductionViol[o] else none) + (o in ExtractProductionOcc => extractProductionViol[o] else none)
  + (o in DistributeOcc => distributeViol[o] else none) + (o in CompleteOcc => completeViol[o] else none)
  + (o in CancelOcc => cancelViol[o] else none)
}

fact DemandAdmissionWitness {
  // the demand log, BY SHAPE (DT-030, 2026-09-09): one witness per shape; the kinds' violation sets are unchanged
  all o: lc/CreateOcc | let v = (o in CreateDemandOcc => createViol[o] else createWithViol[o]) |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/MutateOcc | let v = demandDomainViol[o] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/RetireOcc | let v = deleteViol[o] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  // the delivery log, per kind (a lifecycle adopter since cut 2: pdlc)
  all o: CreateDeliveryOcc   | (o.admission = Accepted iff no createDeliveryViol[o])   and (o.admission in Rejected implies o.admission.because = createDeliveryViol[o])
  all o: RevokeDeliveryOcc   | (o.admission = Accepted iff no revokeDeliveryViol[o])   and (o.admission in Rejected implies o.admission.because = revokeDeliveryViol[o])
  all o: RetireDeliveryOcc   | (o.admission = Accepted iff no retireDeliveryViol[o])   and (o.admission in Rejected implies o.admission.because = retireDeliveryViol[o])
  all o: CompleteOcc         | (o.admission = Accepted iff no completeViol[o])         and (o.admission in Rejected implies o.admission.because = completeViol[o])
  all o: CancelOcc           | (o.admission = Accepted iff no cancelViol[o])           and (o.admission in Rejected implies o.admission.because = cancelViol[o])
  all o: DeleteDemandOcc     | (o.admission = Accepted iff no deleteViol[o])           and (o.admission in Rejected implies o.admission.because = deleteViol[o])
}

// ── effects (committed) — per-kind frames on the record ────────────────────────────────────────
/** sameFields — the notes and the work order are carried over. */
pred sameFields[b, a: DemandState] {
  a.sUserNotes = b.sUserNotes and a.sWorkOrder = b.sWorkOrder and a.sFulfillmentNotes = b.sFulfillmentNotes
}
/** sameDemandButStatus — everything except the status is carried over. */
pred sameDemandButStatus[b, a: DemandState] {
  a.sContributions = b.sContributions and a.sHolding = b.sHolding and sameFields[b, a]
}
/** sameDemandButContributions — everything except the contributions is carried over. */
pred sameDemandButContributions[b, a: DemandState] {
  a.sStatus = b.sStatus and a.sHolding = b.sHolding and sameFields[b, a]
}
/** sameContributionButNotes — two contributions agree on everything a note write leaves alone. */
pred sameContributionButNotes[b, a: Contribution] {
  a.cid = b.cid
  (b in CardContribution) implies (a in CardContribution and a.cycleRef = b.cycleRef and a.referenceOverride = b.referenceOverride)
  (b in ExternalContribution) implies (a in ExternalContribution and a.cPool = b.cPool and a.quantity = b.quantity
                                        and a.externalReference = b.externalReference)
}
/** editedFrom — `a` is `b` with the fields the edit carries set, and every other field kept (dafny-domain's Effect of
    EditContribution: a reference on a card sets its override; a quantity reaches an external contribution only). */
pred editedFrom[b, a: Contribution, o: EditContributionOcc] {
  a.cid = b.cid and a.cUserNotes = b.cUserNotes
  (b in CardContribution) implies {
    a in CardContribution and a.cycleRef = b.cycleRef
    a.referenceOverride = ((some o.newReference) => o.newReference else b.referenceOverride)
  }
  (b in ExternalContribution) implies {
    a in ExternalContribution and a.cPool = b.cPool
    a.quantity = ((some o.newQuantity) => o.newQuantity else b.quantity)
    a.externalReference = ((some o.newReference) => o.newReference else b.externalReference)
  }
}
/** othersKept — every contribution but the one under `id` is carried over. */
pred othersKept[b, a: DemandState, id: EntityId] {
  { c: a.sContributions | c.cid != id } = { c: b.sContributions | c.cid != id }
}
/** sameHolding — the holding ref is carried over (item/station live on the ENTITY now). */
pred sameHolding[b, a: DemandState] { a.sHolding = b.sHolding }

fact DemandEffectWitness {
  all o: CreateDemandOcc | committed[o] implies {
    dPost[o].sStatus = DS_OPEN
    no dPost[o].sContributions                         // born empty (TN-004): the quantity is read from the contributions
    no dPost[o].sHolding
    no dPost[o].sUserNotes and no dPost[o].sWorkOrder and no dPost[o].sFulfillmentNotes
  }
  all o: CreateWithContributionOcc | committed[o] implies {
    dPost[o].sStatus = DS_OPEN
    dPost[o].sContributions = o.contribution           // stored as given: a card's absent override stays absent (MD-077)
    no dPost[o].sHolding
    no dPost[o].sUserNotes and no dPost[o].sWorkOrder and no dPost[o].sFulfillmentNotes
  }
  all o: AddContributionOcc | committed[o] implies {
    dPost[o].sContributions = dPre[o].sContributions + o.contribution
    sameDemandButContributions[dPre[o], dPost[o]]
  }
  all o: RemoveContributionOcc + DetachWithdrawnOcc | committed[o] implies {
    dPost[o].sContributions = { c: dPre[o].sContributions | c.cid != o.target }
    sameDemandButContributions[dPre[o], dPost[o]]
  }
  all o: EditContributionOcc | committed[o] implies {
    sameDemandButContributions[dPre[o], dPost[o]] and othersKept[dPre[o], dPost[o], o.target]
    some b: dPre[o].sContributions, a: dPost[o].sContributions | b.cid = o.target and editedFrom[b, a, o]
  }
  all o: SetContributionNotesOcc | committed[o] implies {
    sameDemandButContributions[dPre[o], dPost[o]] and othersKept[dPre[o], dPost[o], o.target]
    some b: dPre[o].sContributions, a: dPost[o].sContributions |
      b.cid = o.target and sameContributionButNotes[b, a] and a.cUserNotes = o.notes
  }
  all o: SetUserNotesOcc | committed[o] implies {
    dPost[o].sUserNotes = o.notes                      // SET; none given clears it
    dPost[o].sStatus = dPre[o].sStatus and dPost[o].sContributions = dPre[o].sContributions and sameHolding[dPre[o], dPost[o]]
    dPost[o].sWorkOrder = dPre[o].sWorkOrder and dPost[o].sFulfillmentNotes = dPre[o].sFulfillmentNotes
  }
  all o: SetWorkOrderOcc | committed[o] implies {
    dPost[o].sWorkOrder = o.workOrder
    dPost[o].sStatus = dPre[o].sStatus and dPost[o].sContributions = dPre[o].sContributions and sameHolding[dPre[o], dPost[o]]
    dPost[o].sUserNotes = dPre[o].sUserNotes and dPost[o].sFulfillmentNotes = dPre[o].sFulfillmentNotes
  }
  all o: SetFulfillmentNotesOcc | committed[o] implies {
    dPost[o].sFulfillmentNotes = o.notes
    dPost[o].sStatus = dPre[o].sStatus and dPost[o].sContributions = dPre[o].sContributions and sameHolding[dPre[o], dPost[o]]
    dPost[o].sUserNotes = dPre[o].sUserNotes and dPost[o].sWorkOrder = dPre[o].sWorkOrder
  }
  all o: ReleaseOcc | committed[o] implies
    { dPost[o].sStatus = DS_RELEASED and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: ReopenOcc | committed[o] implies
    { dPost[o].sStatus = DS_OPEN and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: StartProductionOcc | committed[o] implies {
    dPost[o].sStatus = DS_IN_PROCESS
    dPost[o].sHolding = o.holding                     // the accumulation pool attaches (R8);
                                                       //   itemPin agreement: StartProductionHoldingPoolPin below
    dPost[o].sContributions = dPre[o].sContributions
    sameFields[dPre[o], dPost[o]]
  }
  all o: RecordProductionOcc | committed[o] implies o.post = o.pre   // ⟲ — the contribution is the PD row (§8.1.2); pool merges are runtime
  all o: ExtractProductionOcc | committed[o] implies o.post = o.pre  // ⟲ — the reversal is the PD's REVOKED row; pool movement is runtime
  all o: DistributeOcc       | committed[o] implies o.post = o.pre   // ⟲ — allocation moves pools + cycles, not this record
  all o: CreateDeliveryOcc   | committed[o] implies pdPost[o].sStatus = PD_CREATED
  all o: RevokeDeliveryOcc   | committed[o] implies pdPost[o].sStatus = PD_REVOKED
  // RetireDeliveryOcc: the tombstone is the family's `pdlc/RetireEffect` (post = pre) — no effect line here (cut 2)
  all o: CompleteOcc | committed[o] implies
    { dPost[o].sStatus = DS_COMPLETE and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: CancelOcc | committed[o] implies
    { dPost[o].sStatus = DS_CANCELED and sameDemandButStatus[dPre[o], dPost[o]] }
  // (DeleteDemandOcc's tombstone: the lifecycle module's `RetireEffect`, since 2026-09-09)
}

// (M3.2, the minted holding pool carries the demand's item pin — DT-020 §8.5.3 / SPEARHEAD-D1 A′-2 — is the RWrongItem arm of
// startProductionViol since QA704 Q4 (a); its law is the theorem tests/unit/demand.als unit_dem_holdingPoolPinHolds.)

// (NO cross-log enforcement facts — C/OP, 2026-07-06: the guards above ARE the saga commit
// gates; the commit-gate contract laws are THEOREMS of them, and the quiescence law
// `demandCyclesAlignedAt` is witnessed on settled traces, never asserted globally.)
