module resources/kanban_card/kanban_card_implementation

/*
 * KanbanCard/CardCycle — IMPLEMENTATION (DT-017 four-file cut, 2026-07-08; machinery from the
 * pre-cut cycle_occurrences.als + kanban_card.als, semantics UNCHANGED): spine adoption
 * (chaining + commit policy), the reason-precise admission guards + witnessing, the per-kind
 * effect frames, and the print machine. The lifecycle discipline (KD9/KQ-S1/KQ-S9) is the
 * ADMISSION GUARD: the canonical region order + the reified LifecycleConfig — a forward
 * operation may SKIP only INACTIVE statuses; TWO sanctioned backward operations: Shelve
 * (REQUESTED → REQUESTING) and ProductionFailure (IN_PROCESS → REQUESTING — DT-016 R8).
 * CLOSURE: withdraw (abandoned) or the successor's genesis (rollover — completed). Cycle
 * occurrences share the ONE causal Tick order with IIOcc/PoolOcc — the composition seam the
 * demand module reads.
 */

open resources/kanban_card/kanban_card_types as kt
open meta/subject_log/subject_log[kt/CardCycle, kt/CycleState] as clog

// ── the spine adoption: chaining (unconditional — refusals read the real state) + v1 commit ────
fact CycleChain         { clog/chained }
fact CycleCommitAccepts { clog/commitAlwaysAccepts }

/** liveAtOcc — the cycle is STARTED and OPEN when `o` executes (what its guards read). */
pred liveAtOcc[o: CycleOcc] { some o.pre and not closedStrictlyBefore[o.subject, o.tick] }

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ───────────────────
/** requestViol — genesis: a fresh cycle, whose predecessor (if any) is rollover-eligible
    (closed, or open at a COMPLETABLE status — the genesis then closes it as completed; MP
    ruling 2026-07-08), into an active REQUESTING. Mid-trip (REQUESTING/REQUESTED/IN_PROCESS)
    refuses: aborting there stays an explicit, auditable Withdraw. */
fun requestViol[o: RequestOcc]: set Reason {
  ((some b: CycleOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick])
     => RAlreadyStarted else none)
  + ((some o.subject.precededBy and not rolloverEligible[o.subject.precededBy, o.tick])
     => RCardInCirculation else none)
  + ((REQUESTING not in LifecycleConfig.active) => RInactiveTarget else none)
  // DT-023 D2/D3 (the kanban matrix row): cycle GENESIS is where the card starts a NEW
  // replenishment episode — scan-to-order of a retired item refuses; the live cycle,
  // once started, completes (grandfathered — no other cycle kind reads item liveness).
  + ((not itemLiveAt[(cycles.(o.subject)).itemPin.subject, o.tick]) => RRetiredRef else none)
}
/** forwardViol — the forward-skip discipline (KD9): strictly forward, into an active status,
    skipping only inactive ones. */
fun forwardViol[o: CycleOcc]: set Reason {
  ((not liveAtOcc[o]) => RClosed else none)
  + ((liveAtOcc[o] and not regionBefore[o.pre.sStatus, targetOf[o]]) => RBackward else none)
  + ((targetOf[o] not in LifecycleConfig.active) => RInactiveTarget else none)
  + ((liveAtOcc[o] and regionBefore[o.pre.sStatus, targetOf[o]]
      and some m: LifecycleConfig.active | regionBetween[m, o.pre.sStatus, targetOf[o]])
     => RSkippedActive else none)
}
// R2 discharge statement (D3, MINESWEEPER model-deltas M1.4): holder EXCLUSIVITY is enforced
// in the DEMAND module by the per-cycle claim log (`cycleIndivisible`/`attachRequiresAccepted`
// — a cycle belongs to at most one live DemandItem, and attach reads the cycle's own ACCEPTED
// state). Kanban contributes only its OWN monotonic guarantees toward that: the forward-only
// `accept` discipline (`RBackward` — a cycle can't be re-requested/re-accepted underneath a
// claim) and the cycle-table fork guard (`RCardInCirculation`/`OneChainPerCard` — at most one
// open cycle per card at a time). No law change here; this module never re-checks demand-side
// exclusivity.
/** startViol — StartProcessing = the forward step PLUS the pool attach: the resolved pool (if it
    resolves — dangling allowed, soft ref) must be in-tenant, not held by another LIVE cycle
    (EXCLUSIVE while the holder lives — Miguel 2026-07-03), classify under the card's demanded
    Item (HOMOGENEITY — DT-015 R1, MP 2026-07-16: sight-of-card, the admission reads the OWNING
    card's itemRef; `cycles.(o.subject)` is unique by CardCycleOwnership; comparison at the
    EntityId level, like the pool-side RWrongItem), and be FRESH (M1, DT-020 §8.5.3 —
    ownership-by-genesis: `pool` is minted inside this act, never a pre-existing pool being
    attached — RPoolNotFresh below). These three arms stay CHECKS over the minted pool; residue
    reaches a cycle's pool only by item-level moves (M2's PoolTransferOcc), never by attaching a
    used pool. */
fun startViol[o: StartProcessingOcc]: set Reason {
  forwardViol[o]
  + ((some p: resolve[o.pool] & InventoryPool | p.tenantId != o.subject.tenantId) => RForeignPool else none)
  + ((some p: resolve[o.pool] & InventoryPool | some c2: CardCycle - o.subject |
        liveCycleAt[c2, o.tick] and resolve[stateOfCycleAt[c2, o.tick].sPool] = p)
     => RPoolInUse else none)
  + ((some p: resolve[o.pool] & InventoryPool | p.itemPin.subject != (cycles.(o.subject)).itemPin.subject)
     => RPoolWrongItem else none)
  + ((some p: resolve[o.pool] & InventoryPool, b: PoolOcc | committed[b] and b.pool = p and precedes[b.tick, o.tick])
     => RPoolNotFresh else none)
}
/** shelveViol — the sanctioned backward operation: exactly REQUESTED → REQUESTING. */
fun shelveViol[o: ShelveOcc]: set Reason {
  ((not liveAtOcc[o]) => RClosed else none)
  + ((liveAtOcc[o] and o.pre.sStatus != REQUESTED) => RNotRequested else none)
  + ((REQUESTING not in LifecycleConfig.active) => RInactiveTarget else none)
}
/** withdrawViol — closing an open cycle. */
fun withdrawViol[o: WithdrawOcc]: set Reason { (not liveAtOcc[o]) => RClosed else none }
/** productionFailureViol — the SECOND sanctioned backward operation (R8, amended 2026-07-06):
    exactly IN_PROCESS → REQUESTING (the completing production run allocated this cycle nothing;
    it re-enters the waiting queue, attachable by a new DemandItem). */
fun productionFailureViol[o: ProductionFailureOcc]: set Reason {
  ((not liveAtOcc[o]) => RClosed else none)
  + ((liveAtOcc[o] and o.pre.sStatus != IN_PROCESS) => RNotInProcess else none)
  + ((REQUESTING not in LifecycleConfig.active) => RInactiveTarget else none)
}

fact CycleAdmissionWitness {
  all o: RequestOcc  | (o.admission = Accepted iff no requestViol[o])  and (o.admission in Rejected implies o.admission.because = requestViol[o])
  all o: cycleForwardOps - StartProcessingOcc | (o.admission = Accepted iff no forwardViol[o]) and (o.admission in Rejected implies o.admission.because = forwardViol[o])
  all o: StartProcessingOcc | (o.admission = Accepted iff no startViol[o]) and (o.admission in Rejected implies o.admission.because = startViol[o])
  all o: ShelveOcc   | (o.admission = Accepted iff no shelveViol[o])   and (o.admission in Rejected implies o.admission.because = shelveViol[o])
  all o: WithdrawOcc | (o.admission = Accepted iff no withdrawViol[o]) and (o.admission in Rejected implies o.admission.because = withdrawViol[o])
  all o: ProductionFailureOcc | (o.admission = Accepted iff no productionFailureViol[o]) and (o.admission in Rejected implies o.admission.because = productionFailureViol[o])
}

// ── effects (committed) — per-kind frames on the record ────────────────────────────────────────
pred sameCyclePayloadButStatus[b, a: CycleState] {
  a.sLocator = b.sLocator and a.sPool = b.sPool and a.sQuantityOverride = b.sQuantityOverride
}
fact CycleEffectWitness {
  all o: RequestOcc | committed[o] implies {
    o.post.sStatus = REQUESTING
    no o.post.sPool                            // the demanding leg carries no bin (KD12 revised)
    o.post.sQuantityOverride = o.qtyOverride
    no (o.post & CycleState).sLocator          // dormant until the rung-4 writer (& CycleState: sLocator is ambiguous vs InventoryItemState since DT-017 brought the II record into the pool cone)
  }
  all o: cycleForwardOps - StartProcessingOcc | committed[o] implies {
    o.post.sStatus = targetOf[o] and sameCyclePayloadButStatus[o.pre, o.post]
  }
  all o: StartProcessingOcc | committed[o] implies {
    o.post.sStatus = IN_PROCESS
    o.post.sPool = o.pool                      // the pool ATTACHES (exclusive while live) and stays frozen
    (o.post & CycleState).sLocator = (o.pre & CycleState).sLocator and o.post.sQuantityOverride = o.pre.sQuantityOverride
  }
  all o: ShelveOcc | committed[o] implies {
    o.post.sStatus = REQUESTING and sameCyclePayloadButStatus[o.pre, o.post]
  }
  all o: WithdrawOcc | committed[o] implies o.post = o.pre      // the TOMBSTONE (closing; abandoned)
  all o: ProductionFailureOcc | committed[o] implies {          // back to the waiting queue (R8)
    o.post.sStatus = REQUESTING
    no o.post.sPool                            // the pool DETACHES — REQUESTED is the demand leg again
    (o.post & CycleState).sLocator = (o.pre & CycleState).sLocator
    o.post.sQuantityOverride = o.pre.sQuantityOverride
  }
}

// ── print lifecycle machine (the durable artifact — KD3; vocabulary in types) ───────────────────
one sig KanbanPrintMachine extends StateMachine {}
abstract sig KPrintTransition extends Transition {}
one sig KPr_print     extends KPrintTransition {} { on = PE_PRINT     and to = PS_PRINTED }
one sig KPr_reprint   extends KPrintTransition {} { on = PE_REPRINT   and to = PS_PRINTED }
one sig KPr_lost      extends KPrintTransition {} { on = PE_LOST      and to = PS_LOST }
one sig KPr_deprecate extends KPrintTransition {} { on = PE_DEPRECATE and to = PS_DEPRECATED }
one sig KPr_retire    extends KPrintTransition {} { on = PE_RETIRE    and to = PS_RETIRED }
one sig KPr_unmark    extends KPrintTransition {} { on = PE_UNMARK    and to = PS_NOT_PRINTED }
one sig KPr_destroy   extends KPrintTransition {} { on = PE_DESTROY   and no to }
one sig KPr_none      extends KPrintTransition {} { on = PE_NONE      and no to }
fact KanbanPrintMachineDef {
  KanbanPrintMachine.states      = KanbanCardPrintStatus
  KanbanPrintMachine.signals     = KanbanCardPrintEventType
  KanbanPrintMachine.start       = PS_NOT_PRINTED
  KanbanPrintMachine.transitions = KPrintTransition
  all t: KPrintTransition | t.from = KanbanCardPrintStatus and no t.guard
}

// Print snapshot consistency (the print lifecycle keeps the machine + snapshot form — low churn).
fact KanbanPrintConsistency {
  all k: KanbanCard | some k.lastPrintEvent implies
    firedInto[KanbanPrintMachine, k.printStatus, k.lastPrintEvent.type]
}
