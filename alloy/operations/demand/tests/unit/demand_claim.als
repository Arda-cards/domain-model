module operations/demand/tests/unit/demand_claim

open operations/demand/demand_claim
open operations/demand/demand_contracts
open meta/intent_log/semantics as sem
open resources/kanban_card/kanban_card_types as kt                // aliased: the parameter below must resolve by ONE path — unqualified,
open meta/intent_log/intent_log[kt/CardCycle, sem/HoldSem] as claim   //   four import paths reach CardCycle here (B-mov's first-execution finding)
open reference_data/item/item_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock

/*
 * THE DEDICATED cycle-claim-chain root (chain A; the demand_reset.als / demand_movement.als confinement precedent): the
 * ONLY unit root that opens demand_claim.als. Witnesses the re-drive cells of DT-027 §6.1 chain A (the arc, the race
 * loser, the lost ack, the uncited UI accept, the three moved-otherwise-under-the-hold cases as COMMITTED RELEASEs, the
 * KEEP round trip, the CLOSE one-row ending, the late accept, the same-owner retry, the RELEASE refused while ours is the
 * head); checks the HELD rule (E5 S-3), the contract laws and the two coupling laws. Scopes follow the demand unit root
 * (kanban mock's print machine 5/8/8/1; 5 Int); kanban rows ride the MOCK (contract assumed), so their admissions are
 * the contract's, not the guards'.
 */

// ── the arc (FM-DEM-24's happy path): RESERVE → the accept cites it → CONFIRM (moved-by-this) → attach adjacent ──
run dem_claimArc {
  some d: DemandItem, c: CardCycle, g: CreateDemandOcc, q: RequestOcc, r: claim/ReserveOcc, k: AcceptOcc, f: claim/ConfirmOcc, a: AddCycleOcc | {
    committed[g] and committed[q] and committed[r] and committed[k] and committed[f] and committed[a]
    g.subject = d and q.subject = c and r.subject = c and k.subject = c and f.subject = c and a.subject = d
    r.holder = d.eId and f.holder = d.eId and k.arche = r and f.peerRid = k and c in resolve[a.member]
    precedes[q.tick, r.tick] and precedes[r.tick, k.tick] and precedes[k.tick, f.tick] and adjacentCommit[f, a]
    f.peerView = sem/PV_MOVED_BY_THIS
    c in attachedLiveAt[d, a.tick] and claimHolderOf[c, a.tick] = d.eId and membershipMirrorsHeadAt[a.tick]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 9 Tick, 8 Occurrence, 10 EntityId, 10 Snapshot expect 1

// The race (FM-DEM-11): two demands RESERVE one cycle — the loser is refused RKeyTaken on the chain BEFORE kanban is
// called; at most one accept exists.
run dem_raceLoserRefused {
  some c: CardCycle, disj a, b: claim/ReserveOcc | {
    committed[a] and refusedAtAdmission[b] and b.admission.because = sem/RKeyTaken
    a.subject = c and b.subject = c and a.holder != b.holder and precedes[a.tick, b.tick]
    lone k: AcceptOcc | committed[k] and k.subject = c
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 8 Snapshot expect 1

// The lost ack (FM-DEM-24): the accept landed and cites the RESERVE, the CONFIRM is lost — the re-drive reads
// RESERVE × moved-by-this from the citation and CONFIRMs without a second accept.
run dem_lostAckRedrive {
  some c: CardCycle, r: claim/ReserveOcc, k: AcceptOcc, t: Tick | {
    committed[r] and committed[k] and r.subject = c and k.subject = c and precedes[r.tick, k.tick] and k.arche = r
    no f: claim/ConfirmOcc | committed[f]
    notAfter[k.tick, t] and claim/phaseAt[c, t] = sem/I_RESERVED and cycleViewAt[c, t] = sem/PV_MOVED_BY_THIS
    claim/redrive[claim/phaseAt[c, t], cycleViewAt[c, t]] = sem/RD_CONFIRM
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 1

// The uncited UI accept (DT-027 §7's cell): the cycle is REQUESTED but nobody's — moved-otherwise → RELEASE, no attach.
run dem_uncitedAcceptReleases {
  some d: DemandItem, c: CardCycle, r: claim/ReserveOcc, k: AcceptOcc, x: claim/ReleaseOcc | {
    committed[r] and committed[k] and committed[x]
    r.subject = c and k.subject = c and x.subject = c and r.holder = d.eId and x.holder = d.eId
    k.arche = k                                                   // a UI accept: self-minted, holds nothing
    precedes[r.tick, k.tick] and precedes[k.tick, x.tick] and statusAt[c, x.tick] = REQUESTED
    cycleViewAt[c, k.tick] = sem/PV_MOVED_OTHERWISE
    claim/redrive[claim/phaseAt[c, k.tick], cycleViewAt[c, k.tick]] = sem/RD_RELEASE
    x.peerView = sem/PV_MOVED_OTHERWISE and claim/phaseAt[c, x.tick] = sem/I_FREE
    no a: AddCycleOcc + CreateWithCycleOcc | committed[a]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 1

// ── moved-otherwise UNDER THE HOLD (A-4), as COMMITTED RELEASEs — what E2b made representable (DT-029 Q9) ──────
// (i) withdrawn: the head is the withdraw, cites nothing of ours → residual MOVED_OTHERWISE → RELEASE + detach-withdrawn.
run dem_withdrawnUnderHoldReleases {
  some d: DemandItem, c: CardCycle, k: AcceptOcc, f: claim/ConfirmOcc, a: AddCycleOcc, w: WithdrawOcc, x: claim/ReleaseOcc, dt: DetachWithdrawnOcc | {
    committed[k] and committed[f] and committed[a] and committed[w] and committed[x] and committed[dt]
    k.subject = c and f.subject = c and w.subject = c and x.subject = c and a.subject = d and dt.subject = d
    f.holder = d.eId and x.holder = d.eId and f.peerRid = k and k.arche in claim/ReserveOcc and c in resolve[a.member] and c in resolve[dt.member]
    precedes[k.tick, f.tick] and adjacentCommit[f, a] and precedes[a.tick, w.tick] and precedes[w.tick, x.tick] and adjacentCommit[x, dt]
    claim/prePhase[x] = sem/I_HELD and x.peerView = sem/PV_MOVED_OTHERWISE
    claim/redrive[sem/I_HELD, cycleViewAt[c, w.tick]] = sem/RD_RELEASE_DETACH
    c not in attachedAt[d, dt.tick] and no claimHolderOf[c, dt.tick]
  }
} for 9 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 11 Tick, 10 Occurrence, 10 EntityId, 12 Snapshot expect 1

// (ii) shelved by a THIRD PARTY (SPEARHEAD-D7 Option A): the head is a stranger's shelve → REQUESTING under the hold reads
// MOVED_OTHERWISE → RELEASE + remove (the cycle is back in the queue, the demand lets go — never a re-accept from under a hold).
run dem_thirdPartyShelveUnderHoldReleases {
  some d: DemandItem, c: CardCycle, k: AcceptOcc, f: claim/ConfirmOcc, a: AddCycleOcc, s: ShelveOcc, x: claim/ReleaseOcc, rm: RemoveCycleOcc | {
    committed[k] and committed[f] and committed[a] and committed[s] and committed[x] and committed[rm]
    k.subject = c and f.subject = c and s.subject = c and x.subject = c and a.subject = d and rm.subject = d
    f.holder = d.eId and x.holder = d.eId and f.peerRid = k and k.arche in claim/ReserveOcc and c in resolve[a.member] and c in resolve[rm.member]
    s.arche = s                                                   // a stranger's shelve: cites nothing of ours
    precedes[k.tick, f.tick] and adjacentCommit[f, a] and precedes[a.tick, s.tick] and precedes[s.tick, x.tick] and adjacentCommit[x, rm]
    claim/prePhase[x] = sem/I_HELD and x.peerView = sem/PV_MOVED_OTHERWISE
    claim/redrive[sem/I_HELD, cycleViewAt[c, s.tick]] = sem/RD_RELEASE_DETACH
    c not in attachedAt[d, rm.tick] and no claimHolderOf[c, rm.tick]
  }
} for 9 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 11 Tick, 10 Occurrence, 10 EntityId, 12 Snapshot expect 1
// (iii) card deleted (FM-DEM-16) has no kind in the model: (i)'s shape.

// ── the sub-intents (D2; LC-IL-08 / LC-IL-09) ─────────────────────────────────────────────────────────────────
// KEEP: ACT_RESERVE(A_START) → the start-processing cites it → ACT_CONFIRM → the head reads as the hold again.
run dem_startKeepRoundTrip {
  some d: DemandItem, c: CardCycle, f: claim/ConfirmOcc, ar: claim/ActReserveOcc, sp: StartProcessingOcc, ac: claim/ActConfirmOcc | {
    committed[f] and committed[ar] and committed[sp] and committed[ac]
    f.subject = c and ar.subject = c and sp.subject = c and ac.subject = c
    f.holder = d.eId and ar.holder = d.eId and ac.holder = d.eId
    ar.act = A_START and sp.arche = ar and ac.peerRid = sp
    precedes[f.tick, ar.tick] and precedes[ar.tick, sp.tick] and precedes[sp.tick, ac.tick]
    claim/phaseAt[c, sp.tick] = sem/I_ACTING
    claim/phaseAt[c, ac.tick] = sem/I_HELD and claim/holderAt[c, ac.tick] = d.eId and statusAt[c, ac.tick] = IN_PROCESS
  }
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 10 Tick, 9 Occurrence, 10 EntityId, 11 Snapshot expect 1

// CLOSE: ACT_RESERVE(A_SHELVE) → the shelve cites it → ONE ACT_CONFIRM ends the hold (key FREE, no holder; FM-DEM-20).
run dem_shelveClosesHoldInOneRow {
  some d: DemandItem, c: CardCycle, f: claim/ConfirmOcc, ar: claim/ActReserveOcc, s: ShelveOcc, ac: claim/ActConfirmOcc | {
    committed[f] and committed[ar] and committed[s] and committed[ac]
    f.subject = c and ar.subject = c and s.subject = c and ac.subject = c
    f.holder = d.eId and ar.holder = d.eId and ac.holder = d.eId
    ar.act = A_SHELVE and s.arche = ar and ac.peerRid = s
    precedes[f.tick, ar.tick] and precedes[ar.tick, s.tick] and precedes[s.tick, ac.tick]
    claim/phaseAt[c, ac.tick] = sem/I_FREE and no claimHolderOf[c, ac.tick] and statusAt[c, ac.tick] = REQUESTING
  }
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 10 Tick, 9 Occurrence, 10 EntityId, 11 Snapshot expect 1

// ── the detector, the retry, the guard that still bites ───────────────────────────────────────────────────────
// The late accept: the RESERVE was RELEASEd (uncited, UNMOVED at REQUESTING) and the accept landed AFTER, citing it.
run dem_lateAcceptDetected {
  some c: CardCycle, r: claim/ReserveOcc, x: claim/ReleaseOcc, k: AcceptOcc | {
    committed[r] and committed[x] and committed[k]
    r.subject = c and x.subject = c and k.subject = c and k.arche = r
    precedes[r.tick, x.tick] and precedes[x.tick, k.tick]
    lateAccept[k]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 1

// A-7: the same owner re-sending its RESERVE while the first is live is refused RKeyTaken — no idempotent-reserve clause.
run dem_sameOwnerRetryRefused {
  some c: CardCycle, disj a, b: claim/ReserveOcc | {
    committed[a] and refusedAtAdmission[b] and b.admission.because = sem/RKeyTaken
    a.subject = c and b.subject = c and a.holder = b.holder and precedes[a.tick, b.tick]
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 7 Tick, 8 EntityId, 7 Snapshot expect 1

// The guard still bites at HELD: while OUR accept is the head, a RELEASE is refused RLanded (the HELD rule's other way).
run dem_releaseAtHeldWhileOursRefused {
  some c: CardCycle, k: AcceptOcc, f: claim/ConfirmOcc, x: claim/ReleaseOcc | {
    committed[k] and committed[f]
    k.subject = c and f.subject = c and x.subject = c and k.arche in claim/ReserveOcc and f.peerRid = k
    precedes[k.tick, f.tick] and precedes[f.tick, x.tick]
    claim/prePhase[x] = sem/I_HELD and x.admission in Rejected and sem/RLanded in x.admission.because
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 1

// ── the laws ──────────────────────────────────────────────────────────────────────────────────────────────────
// THE HELD RULE's theorem check (E5 S-3): at HELD, moved-by-this iff the cycle head cites the current hold.
assert dem_heldViewHeadBased {
  all o: claim/ConfirmOcc + claim/ReleaseOcc | claim/prePhase[o] = sem/I_HELD implies
    ((o.peerView = sem/PV_MOVED_BY_THIS) iff cycleHeadCitesAt[o.subject, o.tick])
}
check dem_heldViewHeadBased for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 10 Snapshot expect 0
assert dem_confirmedAcceptCited { confirmedAcceptCited }
check dem_confirmedAcceptCited for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 10 Snapshot expect 0
// R-a (MINESWEEPER's chain A review): the residual's MOVED_OTHERWISE arm under the hold cannot be reading our own accept in
// flight — at every held tick a committed accept citing the opener strictly precedes it. Negative control: drop `confirmViol`'s
// RNotLanded arm and this check finds the counterexample (an uncited CONFIRM enters HELD with no accept) — run as a probe.
assert dem_heldImpliesAcceptLanded { heldImpliesAcceptLanded }
check dem_heldImpliesAcceptLanded for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 10 Snapshot expect 0
assert dem_releasedClaimUncited { releasedClaimUncited }
check dem_releasedClaimUncited for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 10 Snapshot expect 0
assert dem_attachRequiresHeld { attachRequiresHeld }
check dem_attachRequiresHeld for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 10 Snapshot expect 0
assert dem_detachRequiresReleased { detachRequiresReleased }
check dem_detachRequiresReleased for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 10 Snapshot expect 0
assert dem_cycleIndivisibleFromChain { cycleIndivisibleFromChain }
check dem_cycleIndivisibleFromChain for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem, 1 InventoryPool, 8 Tick, 10 EntityId, 10 Snapshot expect 0
