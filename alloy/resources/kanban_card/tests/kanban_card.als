module resources/kanban_card/tests/kanban_card

open meta/kernel
open shared/values
open meta/state_machine/machine
open reference_data/item/item_mock                  // item laws as CONTRACT (DT-017 consumer unit root)
open resources/inventory_item/inventory_item_types   // InventoryItem (materials soft-ref target) [KC-MH-12]
open resources/processing_network/processing_network_mock   // stub laws as CONTRACT (DT-017 consumer unit root)
open resources/kanban_card/kanban_card_implementation

/*
 * Structural suite for the split KanbanCard + CardCycle model — SLIMMED with DT-015 Phase B: the
 * operational lifecycle moved to the occurrence log (tests/cycle_occurrences.als carries the
 * behavioral claims: guards, closure, one-live-per-card); this root keeps the STRUCTURAL laws
 * (identity, ownership, ordering, refs, the print machine) plus the log-composed card readings.
 * Premises are FACTS via the P1 profile in the cone (the à la carte ScalarPremises fact retired).
 * Machine pins: 5 State / 8 Signal / 8 Transition / 1 StateMachine (print only — the op machine
 * retired). 5 Int: the region ranks reach 8.
 */

// ── SAT: coherent structures ──────────────────────────────────────────────────────────────
// A card in circulation: a 2-cycle chain, c1 closed by ROLLOVER, currentCycleAt = the tail (log).
run unit_kc_twoCycleChainCurrent {
  some k: KanbanCard, disj c1, c2: CardCycle, r2: RequestOcc | {
    k.cycles = c1 + c2
    no c1.precededBy and c2.precededBy = c1
    r2.cycle = c2 and committed[r2]
    currentCycleAt[k, r2.tick] = c2
    some k.itemPin.subject
  }
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 1

// A card OUT of circulation (KC-MH-6): it has cycle history but no live cycle — "AVAILABLE".
run unit_kc_outOfCirculation {
  some k: KanbanCard, t: Tick | some k.cycles and not cardInCirculationAt[k, t]
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 1

// A loaded cycle: IN_USE with its pool attached and stocked, sourced by a (stub) document.
run unit_kc_loadedCycle {
  some c: CardCycle, t: Tick, p: InventoryPool | {
    statusAt[c, t] = IN_USE
    resolve[stateOfCycleAt[c, t].sPool] = p and some heldAt[p, t]
    some c.sourcedBy
  }
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// A card whose loop resolves to a Loop (KC-MH-5).
run unit_kc_cardOnLoop {
  some k: KanbanCard | some l: Loop | resolve[k.loopRef] = l
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 1

// The cycle's pool ref resolves to an actual InventoryPool (the KD12-revised typed seam).
run unit_kc_poolRefResolves {
  some s: CycleState, p: InventoryPool | resolve[s.sPool] = p
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 InventoryItem, 1 InventoryPool, 2 Note expect 1

// The pool carries TWO distinct holdings at once (no Merge forced; the one-vs-set duality lives
// on the POOL, exactly its founding intent).
run unit_kc_multiMaterials {
  some c: CardCycle, t: Tick, p: InventoryPool | {
    resolve[stateOfCycleAt[c, t].sPool] = p
    some disj a, b: InventoryItem | (a + b) in heldAt[p, t]
  }
} for 7 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar,
      9 EntityId, 3 InventoryItem, 1 InventoryPool, 2 CardCycle, 1 KanbanCard, 2 Note expect 1

// ── UNSAT: structural invariants forbid the bad case ────────────────────────────────────────
// The pool ref is typed — it can never resolve to a non-InventoryPool entity.
run unit_kc_poolRefNonPoolImpossible {
  some s: CycleState | let p = resolve[s.sPool] | some p and p not in InventoryPool
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// KC-MH-6: a cycle STATE can never be AVAILABLE (that is card-level; a CycleState record fact).
run unit_kc_cycleAvailableImpossible {
  some s: CycleState | s.sStatus = AVAILABLE
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// Ownership: every cycle belongs to exactly one card — no orphan cycle.
run unit_kc_orphanCycleImpossible {
  some c: CardCycle | no k: KanbanCard | c in k.cycles
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// Ownership: a cycle shared by two cards.
run unit_kc_sharedCycleImpossible {
  some disj a, b: KanbanCard | some c: CardCycle | c in a.cycles and c in b.cycles
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// Ordering: the precededBy chain is acyclic.
run unit_kc_precededCycleImpossible {
  some c: CardCycle | c in c.^precededBy
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// Ordering: linear — no two cycles share a predecessor (no fork).
run unit_kc_forkedChainImpossible {
  some disj a, b: CardCycle | some a.precededBy and a.precededBy = b.precededBy
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// Ordering: precededBy stays within the same card (no cross-card link).
run unit_kc_crossCardPrecededImpossible {
  some disj a, b: KanbanCard, c: a.cycles | some c.precededBy and c.precededBy in b.cycles
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// (The live-cycle laws — one live per card, live = open tail — are THEOREMS of the log now:
// see tests/cycle_occurrences.als `unit_cyc_oneLiveCyclePerCard` and the closure suite.)

// Print snapshot consistency on the card (the print lifecycle keeps the machine form).
run unit_kc_badPrintPairingImpossible {
  some k: KanbanCard | some k.lastPrintEvent and not firedInto[KanbanPrintMachine, k.printStatus, k.lastPrintEvent.type]
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// Serial uniqueness within a tenant.
run unit_kc_serialClashImpossible {
  some disj a, b: KanbanCard | a.tenantId = b.tenantId and a.serialNumber = b.serialNumber
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// Cross-tenant item reference (kernel isolation).
run unit_kc_crossTenantItemImpossible {
  some k: KanbanCard | k.itemPin.subject.tenantId != k.tenantId
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// ── machine-level checks (the PRINT machine — the op machine retired with DT-015 Phase B) ────
check unit_kc_printReachable { allStatesReachable[KanbanPrintMachine] }
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0
check unit_kc_printLiveSignals { liveSignals[KanbanPrintMachine] }
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 0

// ── MPBOT-31 (2026-10-01): the card carries administrative notes — the shared value `Note`, distinct from the occurrence note ──
run unit_kc_cardCarriesNotes {
  some k: KanbanCard | some k.notes
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 Note expect 1
