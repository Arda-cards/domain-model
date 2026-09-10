module resources/inventory_item/tests/metrics

open resources/inventory_item/metrics
open resources/inventory_item/inventory_item_types  // DIRECT (rule 10): `inventory_item_types/CreateOcc` — the module's own kind, disambiguated from the lifecycle family's `lc/CreateOcc` now in the transitive namespace (Tier B 793cfe0 parse red, 2026-09-09)

/*
 * Suite for the INVENTORY-COUNT METRICS module (DT-007 / PDEV-680 — the read side). group/order
 * premises are FACTS via the P2 profile in the cone; `clocksAligned` / `strictChronology` /
 * `calendarAxioms` are assumed PER COMMAND where the property needs them. Scope notes: cells force
 * their contribution lines into existence (2 atoms per member per cell) — size TLine/DLine to
 * cells × members; zero out the measurement family in family-A commands and the report family in
 * bridge commands to keep the (arity-4-carrying) universes small. The family-A theorems (and the
 * cone boundary witness) run at the SMALLEST meaningful counterexample space (2 members, 3/4
 * lines) — at 3 members × 6 lines the fold quantification blows solve time past gate practicality;
 * prefer glucose (`ALLOY_FLAGS='-s glucose'`) — SAT4J needs 15+ min on the partition theorem.
 */

// ── family A: SAT witnesses ───────────────────────────────────────────────────────────────────
// A cell totals two members (the cross-sectional keyed Σ actually sums).
run unit_invmet_countLoads {
  clocksAligned
  some c: CountCell, disj m1, m2: InventoryItem | {
    no c.cLevel
    m1 + m2 in membersOf[c]
    not isZero[cellTotal[c]]
  }
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 3 InventoryItem, 1 CountCell, 2 TLine, 2 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 1

// An EMPTY (consumed-to-zero) member still counts — as a ZERO triple (a line is reported, not dropped).
run unit_invmet_emptyMemberZero {
  clocksAligned
  some c: CountCell, m: InventoryItem | {
    no c.cLevel
    membersOf[c] = m
    stateAsOf[m, c.cAsOf].sFill = EMPTY
    isZero[cellTotal[c]] and isZero[cellDegraded[c]] and isZero[cellUsable[c]]
  }
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 1 CountCell, 1 TLine, 1 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 1

// A retired (deleted) item is EXCLUDED from later counts, even though it matches tenant + Item.
run unit_invmet_retiredExcluded {
  clocksAligned
  some c: CountCell, m: InventoryItem, d: DeleteOcc | {
    committed[d] and d.target = m and atOrBefore[d.at, c.cAsOf]
    no c.cLevel and m.tenantId = c.cTenant and m.itemPin.subject = c.cItem
    m not in membersOf[c]
  }
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 1 CountCell, 2 TLine, 2 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 1

// A2 locator classification: a facility-level cell admits the in-prefix member and excludes a
// live, same-Item member located elsewhere.
run unit_invmet_locatorCellLoads {
  clocksAligned
  some c: CountCell, disj m1, m2: InventoryItem | {
    c.cLevel = LFacility
    m1 in membersOf[c]
    liveAsOf[m2, c.cAsOf] and m2.tenantId = c.cTenant and m2.itemPin.subject = c.cItem
    m2 not in membersOf[c]
  }
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 1 CountCell, 2 TLine, 2 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 1

// The level JUMPS at a committed write: two same-query cells straddling a Replenish differ.
run unit_invmet_levelJumps {
  clocksAligned
  some disj c1, c2: CountCell, r: ReplenishOcc | {
    c1.cTenant = c2.cTenant and c1.cItem = c2.cItem and no c1.cLevel and no c2.cLevel
    committed[r] and r.target in membersOf[c2]
    earlierThan[c1.cAsOf, r.at] and atOrBefore[r.at, c2.cAsOf]
    cellTotal[c1] != cellTotal[c2]
  }
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 2 CountCell, 3 TLine, 3 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 1

// ── family A: theorems (check; UNSAT = holds) ───────────────────────────────────────────────────
// CONSERVATION + REFINEMENT in one law: a cell partitioned into two disjoint covering cells has
// additive totals (locator subtotals tie out to the item total; coarser nodes = Σ of finer).
assert unit_invmet_partitionAdditivity {
  all z, x, y: CountCell |
    (x.cAsOf = z.cAsOf and y.cAsOf = z.cAsOf
     and (let zL = { l: TLine | l.tCell = z }, xL = { l: TLine | l.tCell = x }, yL = { l: TLine | l.tCell = y } |
            no (xL.tMember & yL.tMember) and zL.tMember = xL.tMember + yL.tMember))
    implies cellTotal[z] = add[cellTotal[x], cellTotal[y]]
}
// NB the antecedent is stated over the LINES (CellLinesExact pins them 1:1 to members), not by
// recomputing membersOf four times — the recomputation made this check pathologically slow.
check unit_invmet_partitionAdditivity for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 4 InventoryItemState, 2 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 4 Tick, 4 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 3 CountCell, 4 TLine, 4 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 0

// BOUNDARY WITNESS (a deliberate NON-theorem): per-member cone-safety (degraded ≤ actual — a
// record FACT, G4) does NOT lift through the Σ at the abstract-scalar level. `orderAxioms` is only
// a total order — translation invariance (a ≤ b ⟹ a+c ≤ b+c) is deliberately absent because NO
// finite group admits it (positivity cannot survive wrap-around; the same reason the order is a
// posited premise at all). So an aggregate usable CAN classify NEGATIVE under the minimal
// premises; cone-safety of aggregates returns only in concrete realizations with a true
// (unbounded) integer order. Conservative-claims convention: we WITNESS the boundary rather than
// assert a theorem the algebra cannot support.
run unit_invmet_usableConeNotLiftable {
  some c: CountCell | classify[cellUsable[c]] = NEGATIVE
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 4 InventoryItemState, 2 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 4 Tick, 4 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 2 CountCell, 3 TLine, 3 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 1

// A QUIET window repeats the level (LOCF): no committed occurrence in (τ₁, τ₂] ⟹ same members,
// same total — the family-B "a period with no change repeats the prior count".
assert unit_invmet_quietPeriodRepeats {
  clocksAligned implies
  all disj c1, c2: CountCell |
    (c1.cTenant = c2.cTenant and c1.cItem = c2.cItem and no c1.cLevel and no c2.cLevel
     and atOrBefore[c1.cAsOf, c2.cAsOf]
     and (no o: IIOcc | committed[o] and earlierThan[c1.cAsOf, o.at] and atOrBefore[o.at, c2.cAsOf]))
    implies (membersOf[c1] = membersOf[c2] and cellTotal[c1] = cellTotal[c2])
}
check unit_invmet_quietPeriodRepeats for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 4 InventoryItemState, 2 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 4 Tick, 4 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 2 CountCell, 3 TLine, 3 DLine, 0 PeriodSpec, 0 TimeZone, 0 Signal, 0 Measurement
      expect 0

// ── family B: the calendar sampling ─────────────────────────────────────────────────────────────
// A series point loads: a cell evaluated AT a period close (endOfPeriod under calendarAxioms)
// counts a committed member — B is A sampled at the close.
run unit_invmet_periodSeriesLoads {
  clocksAligned and calendarAxioms
  some cal: CalendarSpec, c: CountCell, o: inventory_item_types/CreateOcc | {
    committed[o]
    no c.cLevel
    c.cAsOf = endOfPeriod[cal, o.at]
    o.target in membersOf[c]
  }
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 1 CountCell, 1 TLine, 1 DLine, 1 PeriodSpec, 1 TimeZone, 0 Signal, 0 Measurement
      expect 1

// ── the DT-008 bridge ───────────────────────────────────────────────────────────────────────────
// The bridge loads (also the non-vacuity witness for clocksAligned ∧ strictChronology): a level
// signal with two log-emitted samples at distinct instants.
run unit_invmet_bridgeLoads {
  clocksAligned and strictChronology
  some s: IILevelSignal, disj m1, m2: Measurement | {
    m1.of = s and m2.of = s and m1.at != m2.at
  }
} for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 0 CountCell, 0 TLine, 0 DLine, 0 PeriodSpec, 0 TimeZone, 1 Signal, 2 Measurement
      expect 1

// THE RE-POINT THEOREM (DT-007 ↔ DT-008): the measurement framework's LOCF read equals the log's
// as-of projection — "as-of τ" IS "the last measurement with effective-time ≤ τ".
assert unit_invmet_frameworkMatchesLog {
  (clocksAligned and strictChronology) implies
    all s: IILevelSignal, t: Instant | valueAt[s, t] = stateAsOf[s.watches, t].sActual
}
check unit_invmet_frameworkMatchesLog for 4 but 4 Int, 3 Scalar, 8 Quantity, 3 Unit, 8 EntityId, 2 Item, 2 ItemSupply, 2 UomScheme, 5 InventoryItemState, 3 LicensePlate, 0 SerialNumber, 0 Individualizer, 0 LotNumber, 0 Text, 0 Money, 0 Currency, 3 PhysicalLocator, 5 Label, 5 Tick, 5 Instant, 1 Duration, 0 TimeInterval, 0 Metric, 0 Report, 2 InventoryItem, 0 CountCell, 0 TLine, 0 DLine, 0 PeriodSpec, 0 TimeZone, 1 Signal, 4 Measurement
      expect 0
