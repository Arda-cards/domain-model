module operations/demand/tests/unit/delivery_retire
// Reflects dafny-domain src/operations/demand/tests/demand-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_mock                            // lower layer as CONTRACT (DT-017)
open resources/processing_network/processing_network_mock    // Station stub as CONTRACT
open resources/kanban_card/kanban_card_mock                   // kanban as CONTRACT (DT-017)
open operations/demand/demand_types as dt                     // DIRECT (rule 10): the parameters below are alias-qualified
open meta/subject_log/lifecycle[dt/ProductionDelivery, dt/PDState] as pdlc   // the SHAPES for the delivery log (the cut's second instance)

/*
 * RED-FIRST witnesses for the production-delivery RETIRE kind (DT-030 M2 — a retire kind is mandatory for every
 * Universe-managed entity; Q24 (a): `RetireDeliveryOcc extends pdlc/RetireOcc`, refusals `RDeliveryClosed` (not started /
 * already retired) and `RNotTerminal` (status still PD_CREATED — the demand's two-step: Revoke first, then Retire).
 * Written and run RED at 1e79b89 BEFORE the sig lands (team-operations.md § Test-driven development; model-changes-sequence.md §9):
 * the root fails to parse on `RetireDeliveryOcc` / `pdlc`. One witness per behaviour and per branch of each pair.
 * Scopes: the demand unit root's delivery commands (1 ProductionDelivery; 11 Tick / 11 EntityId / 10 Snapshot / 10 Occurrence).
 * RE-SIZED with the TN-004 projection (2026-11-13; Copilot's review of domain-model PR #12): with no card cycle the delivery's
 * demand reaches IN_PROCESS only through an external contribution and its pool, so a committed create pair COUNTS 10
 * occurrences and a revoke pair 12 (measured: found at 12 and 14 by the one-activation twins). Each witness below has its
 * count and two spare; `unit_pdr_retireNeverCreatedRefused` needs no delivery and keeps its scope.
 * THE ROWS ARE NAMED AND ORDERED in the four witnesses that had no verdict in 1,800 s at these scopes (2026-11-14, a scope and
 * symmetry read, after the order's Submit arc: no verdict unpinned, found in 285 s pinned). A finder needs one history, not
 * every interleaving of the fixtures: `pinnedCreatePair` names the seven rows a committed create pair needs and fixes one
 * order of their ticks. The calls stay free (one per service is counted, a refused row brings its own), and so do the scopes.
 */

/** pinnedCreatePair — ONE order of the seven rows behind a committed create pair of `d`: the item's version, the pool's
    Create, the demand's create with its external contribution, its Release, its StartProduction, then the delivery's Create
    and the RecordProduction naming it (those two in either order). */
pred pinnedCreatePair[d: DemandItem, vi: CreateItemOcc, vp: CreatePoolOcc, dc: CreateWithContributionOcc, dr: ReleaseOcc,
                      dsp: StartProductionOcc, cd: CreateDeliveryOcc, rp: RecordProductionOcc] {
  committed[vi] and committed[vp] and committed[dc] and committed[dr] and committed[dsp] and committed[cd] and committed[rp]
  dc.subject = d and dr.subject = d and dsp.subject = d and rp.subject = d
  cd.subject.demandRef = d.eId and rp.delivery = cd.subject.eId
  precedes[vi.tick, vp.tick] and precedes[vp.tick, dc.tick] and precedes[dc.tick, dr.tick] and precedes[dr.tick, dsp.tick]
  precedes[dsp.tick, cd.tick] and precedes[dsp.tick, rp.tick]
}

/** pinnedRevokePair — the committed revoke pair of the delivery `cd` created, after its create pair: the Revoke and the
    ExtractProduction naming it (in either order). */
pred pinnedRevokePair[d: DemandItem, cd: CreateDeliveryOcc, rp: RecordProductionOcc, v: RevokeDeliveryOcc, x: ExtractProductionOcc] {
  committed[v] and committed[x]
  v.subject = cd.subject and x.subject = d and x.delivery = cd.subject.eId
  precedes[cd.tick, v.tick] and precedes[rp.tick, v.tick] and precedes[cd.tick, x.tick] and precedes[rp.tick, x.tick]
}

// ── the act commits on a REVOKED delivery (terminal) and tombstones it ─────────────────────────
run unit_pdr_retireAfterRevoke {
  some d: DemandItem, vi: CreateItemOcc, vp: CreatePoolOcc, dc: CreateWithContributionOcc, dr: ReleaseOcc, dsp: StartProductionOcc,
       cd: CreateDeliveryOcc, rp: RecordProductionOcc, v: RevokeDeliveryOcc, x: ExtractProductionOcc, o: RetireDeliveryOcc | {
    committed[o] and pdPre[o].sStatus = PD_REVOKED and o.post = o.pre
    pinnedCreatePair[d, vi, vp, dc, dr, dsp, cd, rp] and pinnedRevokePair[d, cd, rp, v, x]
    o.subject = cd.subject and precedes[v.tick, o.tick] and precedes[x.tick, o.tick]
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      15 Tick, 14 EntityId, 16 Snapshot, 15 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1

// ── refused while the delivery is still CREATED (not terminal) — the demand's two-step ─────────
run unit_pdr_retireNotTerminalRefused {
  some o: RetireDeliveryOcc | refusedAtAdmission[o] and o.admission.because = RNotTerminal
    and some o.pre and pdPre[o].sStatus = PD_CREATED
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      13 Tick, 14 EntityId, 14 Snapshot, 13 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1

// ── refused on a delivery that never started (no history) — the generic arm, the adopter's atom ─
run unit_pdr_retireNeverCreatedRefused {
  some o: RetireDeliveryOcc | refusedAtAdmission[o] and o.admission.because = RDeliveryClosed and no o.pre
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery,
      11 Tick, 11 EntityId, 10 Snapshot, 10 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1

// ── refused twice: a second retire after a committed one ───────────────────────────────────────
run unit_pdr_retireTwiceRefused {
  some d: DemandItem, vi: CreateItemOcc, vp: CreatePoolOcc, dc: CreateWithContributionOcc, dr: ReleaseOcc, dsp: StartProductionOcc,
       cd: CreateDeliveryOcc, rp: RecordProductionOcc, v: RevokeDeliveryOcc, x: ExtractProductionOcc, disj r1, r2: RetireDeliveryOcc | {
    committed[r1] and r2.subject = r1.subject and precedes[r1.tick, r2.tick]
    refusedAtAdmission[r2] and RDeliveryClosed in r2.admission.because
    pinnedCreatePair[d, vi, vp, dc, dr, dsp, cd, rp] and pinnedRevokePair[d, cd, rp, v, x]
    r1.subject = cd.subject and precedes[v.tick, r1.tick] and precedes[x.tick, r1.tick]
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      16 Tick, 14 EntityId, 16 Snapshot, 16 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1

// ── complement of the pair: a Revoke after a committed retire is refused (the log is closed) ───
run unit_pdr_revokeAfterRetireRefused {
  some d: DemandItem, vi: CreateItemOcc, vp: CreatePoolOcc, dc: CreateWithContributionOcc, dr: ReleaseOcc, dsp: StartProductionOcc,
       cd: CreateDeliveryOcc, rp: RecordProductionOcc, v0: RevokeDeliveryOcc, x: ExtractProductionOcc, r: RetireDeliveryOcc, v: RevokeDeliveryOcc | {
    committed[r] and v.subject = r.subject and precedes[r.tick, v.tick]
    refusedAtAdmission[v] and RDeliveryClosed in v.admission.because
    pinnedCreatePair[d, vi, vp, dc, dr, dsp, cd, rp] and pinnedRevokePair[d, cd, rp, v0, x]
    r.subject = cd.subject and precedes[v0.tick, r.tick] and precedes[x.tick, r.tick]
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      16 Tick, 14 EntityId, 16 Snapshot, 16 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1

// ── MPBOT-11 M2 (2026-10-01) — the recording law on the delivery log: refused vs recorded ─────
// witness: a refused delivery genesis is NOT recorded; a refused revoke on a CREATED delivery IS
run unit_pdr_refusedGenesisNotRecordedRevokeOnLiveRecorded {
  some d: DemandItem, vi: CreateItemOcc, vp: CreatePoolOcc, dc: CreateWithContributionOcc, dr: ReleaseOcc, dsp: StartProductionOcc,
       cd: CreateDeliveryOcc, rp: RecordProductionOcc, c: CreateDeliveryOcc, r: RevokeDeliveryOcc | {
    refusedAtAdmission[c] and not pdlc/recorded[c]
    refusedAtAdmission[r] and pdlc/liveAt[r] and pdlc/recorded[r]
    pinnedCreatePair[d, vi, vp, dc, dr, dsp, cd, rp]
    r.subject = cd.subject and precedes[cd.tick, r.tick] and precedes[rp.tick, r.tick]
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 ProductionDelivery, 2 Contribution, 0 Placement,
      16 Tick, 15 EntityId, 15 Snapshot, 16 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1

// ── Laws of this root with no check here (the project owner's ruling QA835, option (ii), 2026-11-18) ──────────
// 3 checks left this root with that ruling: a check of a law the reference model proves is retired once every
// premise of its lemma is established. alloy/RETIRED-CHECKS.md names each with its lemma, the lemma's premises and
// why the lemma implies the check. The finders of this root are the laws' witnesses here.
