module operations/demand/tests/unit/demand_movement

open operations/demand/demand_movement
open operations/demand/demand_contracts
open meta/intent_log/semantics as sem
open resources/inventory_item/inventory_pool as ip                 // aliased: the parameter below must resolve by ONE path — unqualified,
open meta/intent_log/intent_log[ip/InventoryPool, sem/MoveSem] as movement   //   four import paths reach InventoryPool here (the soak slices' kt/ pattern)
open reference_data/item/item_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock

/*
 * THE DEDICATED pool-movement-chain root (B-mov; the demand_reset.als confinement precedent): the ONLY unit root
 * that opens demand_movement.als. Witnesses the register's three movement records (R-02 / R-03 / R-05), Q7 = A,
 * the late-act detector and its reversal exclusion; checks the two additive-arm laws. Scopes follow the demand
 * unit root (kanban mock's print machine 5/8/8/1; 5 Int) with the pool atoms this chain needs.
 */

// R-02 (FM-DEM-01) — the merge arc: originator → RESERVE on the holding pool → the add cites it → CONFIRM moved-by-this.
// cut 2b (2026-09-15): `for` raised by ONE — the fix. Since cut 2 the genesis row is mandatory before any mutation (DT-030 M2), one more
//   top-level atom than the old scope allowed (controls: top+1 with the original ticks SAT; wider ticks at the old top UNSAT; `no <genesis>` at the
//   SAT scope UNSAT). The stated CreatePoolOcc row below makes the reason legible; it is not what fixes the witness.
run mov_mergeArc {
  some d: DemandItem, p: InventoryPool, g: RecordProductionOcc, r: movement/ReserveOcc, a: PoolAddOcc, f: movement/ConfirmOcc | {
    committed[g] and committed[r] and committed[a] and committed[f]
    g.subject = d and r.subject = p and a.pool = p and f.subject = p
    r.holder = d.eId and f.holder = d.eId and r.arche = g and a.arche = r and f.peerRid = a
    precedes[g.tick, r.tick] and precedes[r.tick, a.tick] and precedes[a.tick, f.tick]
    f.peerView = sem/PV_MOVED_BY_THIS
    some c0: ip/CreatePoolOcc | committed[c0] and c0.subject = p and precedes[c0.tick, r.tick]   // the pool's genesis, STATED for legibility (not needed by the witness)
  }
} for 10 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 11 Tick, 10 EntityId, 12 Snapshot expect 1

// R-02 — the idempotent callee: a re-sent merge citing the SAME leg on the SAME pool is refused RDuplicateOrigin.
run mov_holdingMergeIdempotent {
  some p: InventoryPool, r: movement/ReserveOcc, disj a, b: PoolAddOcc | {
    committed[r] and committed[a]
    r.subject = p and a.pool = p and b.pool = p and a.arche = r and b.arche = r
    precedes[r.tick, a.tick] and precedes[a.tick, b.tick]
    b.admission in Rejected and RDuplicateOrigin in b.admission.because
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 2 InventoryItem, 1 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 1

// R-03 (FM-DEM-02, PDEV-1772) — two extract legs on ONE holding pool (two revokes): the second RESERVE is refused
// RKeyTaken while the first is live — the loser forks BEFORE any pool row; inventory is called once.
run mov_revokeRaceSerializes {
  some p: InventoryPool, disj g1, g2: ExtractProductionOcc, disj r1, r2: movement/ReserveOcc | {
    committed[g1] and committed[g2] and committed[r1] and g1.subject = g2.subject
    r1.subject = p and r2.subject = p and r1.arche = g1 and r2.arche = g2
    precedes[r1.tick, r2.tick] and movement/phaseAt[p, r2.tick] = sem/I_RESERVED
    r2.admission in Rejected and sem/RKeyTaken in r2.admission.because
  }
} for 9 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 2 ProductionDelivery,
      15 Tick, 14 Occurrence, 14 EntityId, 16 Snapshot expect 1   // scope derived (first execution UNSAT at 11 Tick / for 9): two extracts need
      // two revokes (revokeExtractsAtomically, one extract per revoke), two deliveries (a revoked PD refuses a second revoke), two record +
      // create-delivery pairs, the demand at IN_PROCESS (create, release, start) — 14 occurrences with the two RESERVEs and the item pin

// R-05 (FM-DEM-04) — the interrupted distribute: the extract landed and cites its leg, the demand's DISTRIBUTE is lost;
// the re-drive reads RESERVE × moved-by-this from the citation (`citedAt`) and CONFIRMs without a second extract.
// cut 2b (2026-09-15): `for` raised by ONE — the fix. Since cut 2 the genesis row is mandatory before any mutation (DT-030 M2), one more
//   top-level atom than the old scope allowed (controls: top+1 with the original ticks SAT; wider ticks at the old top UNSAT; `no <genesis>` at the
//   SAT scope UNSAT). The stated CreatePoolOcc row below makes the reason legible; it is not what fixes the witness.
run mov_interruptedDistributeRedrives {
  some p: InventoryPool, g: DistributeOcc, r: movement/ReserveOcc, x: PoolRemoveOcc, f: movement/ConfirmOcc, t: Tick | {
    committed[g] and committed[r] and committed[x] and committed[f]
    r.subject = p and x.pool = p and f.subject = p and r.arche = g and x.arche = r and f.peerRid = x
    precedes[g.tick, r.tick] and precedes[r.tick, x.tick] and precedes[x.tick, t] and precedes[t, f.tick]
    movement/phaseAt[p, t] = sem/I_RESERVED and movement/citedAt[p, t]
    movement/redrive[movement/phaseAt[p, t], sem/PV_MOVED_BY_THIS] = sem/RD_CONFIRM
    no y: PoolRemoveOcc - x | committed[y] and y.arche = r
    some c0: ip/CreatePoolOcc | committed[c0] and c0.subject = p and precedes[c0.tick, r.tick]   // the pool's genesis, STATED for legibility (not needed by the witness)
  }
} for 10 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 11 Tick, 10 EntityId, 12 Snapshot expect 1

// Q7 = A — the transfer composite: ONE leg keyed on the source, its two pool rows on two pools carry ONE arche; the
// paired add is admitted by PoolCitations' transfer clause; CONFIRM cites the transfer row.
run mov_transferBothHalvesOneArche {
  some disj p, q: InventoryPool, l: TransferLeg, o: PoolTransferOcc, a: PoolAddOcc, f: movement/ConfirmOcc | {
    committed[l] and committed[o] and committed[a] and committed[f]
    l.subject = p and resolve[l.moveTo] = q and o.pool = p and o.to = q and a.pool = q and f.subject = p
    o.arche = l and a.arche = l and adjacentCommit[o, a] and f.peerRid = o
    precedes[l.tick, o.tick] and precedes[a.tick, f.tick]
  }
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 2 InventoryPool, 10 Tick, 9 Occurrence, 10 EntityId, 10 Snapshot expect 1
      // scope derived (first execution UNSAT at for 6): the transfer needs the item HELD at the source (poolTransferViol RNotMember) — a
      // prior committed add on p — so 7 occurrences (add, leg, transfer, paired add, confirm, the item pin, a demand row for ownerVersion)

// The transfer's paired add is NOT late (MINESWEEPER's de9b305 review): it cites the leg keyed on the SOURCE while sitting on the
// destination, whose chain may be empty — the detector must read the CITED leg's chain, never the row's own pool.
run mov_pairedAddNotLate {
  some disj p, q: InventoryPool, l: TransferLeg, o: PoolTransferOcc, a: PoolAddOcc | {
    committed[l] and committed[o] and committed[a]
    l.subject = p and resolve[l.moveTo] = q and o.pool = p and o.to = q and a.pool = q
    o.arche = l and a.arche = l and adjacentCommit[o, a] and precedes[l.tick, o.tick]
    no movement/IntentOcc & subject.q                         // the destination has NO chain: phaseAt reads I_FREE there
    not lateMovement[a]
  }
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 2 InventoryPool, 10 Tick, 9 Occurrence, 10 EntityId, 10 Snapshot expect 1
// … and never late while its leg is live: a committed paired add under a RESERVED/HELD source leg is not a late movement (at de9b305,
// which read the destination's empty chain, this check was SAT — the held failure this check guards against).
assert mov_pairedAddNeverLateWhileLegLive {
  all a: PoolAddOcc, tr: PoolTransferOcc | (committed[a] and committed[tr] and tr.to = a.pool and adjacentCommit[tr, a] and tr.arche = a.arche
      and tr.arche in movement/IntentOcc and movement/phaseAt[(tr.arche & movement/IntentOcc).subject, a.tick] in sem/livePhases)
    implies not lateMovement[a]
}
check mov_pairedAddNeverLateWhileLegLive for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 0

// An UNCITED committed add is never late (MINESWEEPER's MG-12 review): the guard `o.arche in movement/IntentOcc` is what excludes it, and
// it excludes it only because `arche` is TOTAL (a self-minted row cites itself, a PoolOcc). Drop the guard — or let the totality move so an
// empty arche reads `none in IntentOcc` as true — and `phaseAt[none, t]` reads I_FREE and this witness goes UNSAT. The doc note's check.
run mov_uncitedAddNotLate {
  some p: InventoryPool, a: PoolAddOcc | {
    committed[a] and a.pool = p and a.arche = a                 // self-minted: no caller context
    no movement/IntentOcc                                        // no intent row anywhere: the only chain reads I_FREE by default
    (no q: PoolAddOcc | q.reverses = a) and (no q: PoolRemoveOcc | q.reverses = a) and (no q: PoolTransferOcc | q.reverses = a)
                                                                 // NO reversal of `a` — run 1's control (mg12fix-5953d11) escaped through a
                                                                 // committed remove reversing the add (instance read, XML): the witness was
                                                                 // not yet a check on the guard. With this, dropping the guard reads the empty
                                                                 // key as I_FREE and the add as late: `not lateMovement[a]` goes UNSAT.
    not lateMovement[a]
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 6 Tick, 6 EntityId, 6 Snapshot expect 1

// The late-act detector: the leg was RELEASEd (uncited, UNMOVED) and the add landed AFTER — a late movement.
run mov_lateMovementDetected {
  some p: InventoryPool, r: movement/ReserveOcc, rel: movement/ReleaseOcc, a: PoolAddOcc | {
    committed[r] and committed[rel] and committed[a]
    r.subject = p and rel.subject = p and a.pool = p and a.arche = r
    precedes[r.tick, rel.tick] and precedes[rel.tick, a.tick]
    lateMovement[a]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 1

// The reversal exclusion: a committed remove naming the late add takes it out of the detector.
// cut 2b (2026-09-15): `for` raised by ONE — the fix. Since cut 2 the genesis row is mandatory before any mutation (DT-030 M2), one more
//   top-level atom than the old scope allowed (controls: top+1 with the original ticks SAT; wider ticks at the old top UNSAT; `no <genesis>` at the
//   SAT scope UNSAT). The stated CreatePoolOcc row below makes the reason legible; it is not what fixes the witness.
run mov_reversalExcluded {
  some p: InventoryPool, r: movement/ReserveOcc, rel: movement/ReleaseOcc, a: PoolAddOcc, x: PoolRemoveOcc | {
    committed[r] and committed[rel] and committed[a] and committed[x]
    r.subject = p and rel.subject = p and a.pool = p and a.arche = r and x.pool = p and x.reverses = a
    precedes[r.tick, rel.tick] and precedes[rel.tick, a.tick] and precedes[a.tick, x.tick]
    not lateMovement[a]
    some c0: ip/CreatePoolOcc | committed[c0] and c0.subject = p and precedes[c0.tick, r.tick]   // the pool's genesis, STATED for legibility (not needed by the witness)
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 1
      // ORIGINAL scope restored: the six-occurrence count was right; the first-execution UNSAT was the LAW TEXT (lateMovement's split
      // nested its quantifiers by precedence and never saw the remove) — found by the bisection probe, fixed in the module

// ── the additive-arm laws (theorems of citationView + the guards) ───────────────────────────────────────────────
assert mov_confirmedMovementCited { confirmedMovementCited }
check mov_confirmedMovementCited for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 0
assert mov_releasedReserveUncited { releasedReserveUncited }
check mov_releasedReserveUncited for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 8 Tick, 8 EntityId, 8 Snapshot expect 0
// One leg per pool per originator (DT-029 Q8): two committed legs on ONE pool citing ONE originator is unrepresentable
// (the module fact `ArcheUnique`); the second is refused RDuplicateArche by `reserveViol` (MG-10).
run mov_secondLegSameOriginRefused {
  some p: InventoryPool, g: DistributeOcc, disj r1, r2: movement/ReserveOcc, f: movement/ConfirmOcc | {
    committed[g] and committed[r1] and committed[f]
    r1.subject = p and r2.subject = p and f.subject = p and r1.arche = g and r2.arche = g
    precedes[r1.tick, f.tick] and precedes[f.tick, r2.tick]
    r2.admission in Rejected and sem/RDuplicateArche in r2.admission.because
  }
} for 9 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 11 Tick, 10 EntityId, 12 Snapshot expect 1
