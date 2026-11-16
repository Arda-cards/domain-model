module operations/demand/demand_quantity

/*
 * DEMAND — the CONFINED QUANTITY READ (TN-004; reflects dafny-domain `DemandQuantityAt`, MD-076). Opened ONLY by its
 * dedicated root (tests/unit/demand_quantity.als). It takes the place of demand_reset.als: the stored, advisory intent and
 * its reset left the reference model, and a demand's quantity is now a READ — the keyed sum of its LIVE contributions'
 * quantities (a card contribution's is its cycle's effective quantity, an external contribution's is its own).
 *
 * WHY CONFINED, AND WHY CASE-WISE (the finding of 2026-07-06, unchanged): the demand cone cannot carry the keyed_sum fold —
 * the transitive vocabulary (kanban + inventory item + item) fixes ~250 atoms into every universe, past Kodkod's ~215-atom
 * arity-4 ceiling. So the sum is stated for the witness sizes (0, 1 and 2 live contributions — exact) and is EMPTY beyond
 * them HERE; the dedicated root's scopes stay within those sizes. The reference model proves the read for any number of
 * contributions (`QuantityIsSumOfLiveContributions`): this module is a finder's vocabulary, not a law.
 */

open operations/demand/demand_implementation

/** demandQuantityAt — the demand's quantity as of `t`, as a keyed map: the sum of the live contributions' quantities.
    Case-wise: no live contribution reads the keyed zero (the empty map); one reads its own; two read their sum. */
fun demandQuantityAt[d: DemandItem, t: Tick]: Unit -> lone Scalar {
  let cs = liveContributionsAt[d, t] |
    (no cs) => (none -> none)
    else ((one cs) => contributionQtyMap[cs]
    else { u: Unit, x: Scalar | #cs = 2 and some disj a, b: cs | u -> x in add[contributionQtyMap[a], contributionQtyMap[b]] })
}
