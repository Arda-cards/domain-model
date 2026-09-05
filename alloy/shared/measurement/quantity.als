module shared/measurement/quantity

/*
 * V = Quantity instantiation of meta/measurement — the value-dependent statistics that need the
 * keyed value algebra (`meta/keyed_value_algebra/*`). LAST/FIRST/COUNT come from the generic module unchanged.
 *   MIN / MAX — over the period's values, via the keyed PARTIAL order (lone; present only when the
 *               values are pairwise comparable — typically a single-unit signal). Documented caveat.
 *   SUM       — the keyed Σ of a period's values, via the parameterized `keyed_sum[Measurement]` fold:
 *               the Fold's `val` = each measurement's value, `earlier` = the same-signal time
 *               predecessor; `sumIn` reads the period sub-chain total (`rangeSum`). Returns the raw keyed
 *               map (not a Quantity atom). MEAN deferred (needs division, absent from the keyed monoid).
 *
 * NB the CROSS-SECTIONAL Σ (the by-Item total / CardCycle consolidation) is event-sourced UPSTREAM
 * (DT-006): a LEVEL signal's value is the running total of signed deltas, emitted as the measurement
 * value (ex14) and read back by LAST — so the framework needs no special sum for the inventory LEVEL
 * report. This module is the framework-side value-statistics; SUM here is the FLOW-signal temporal total.
 */

open shared/values as va // Quantity
open meta/keyed_value_algebra/keyed_order                 // lte (componentwise partial order), classify; → keyed_monoid add/zero
open meta/measurement/measurement[va/Quantity] as me // Signal, Measurement, measurementsIn, latestIn/firstIn, lastValueIn, …
open meta/keyed_value_algebra/keyed_sum[me/Measurement]      // Fold over Measurement, rangeSum (the Σ-along-order fold)

// ── MIN / MAX over a period's values (keyed PARTIAL order — lone; exists iff pairwise comparable) ──
/** MIN — the period value ≤ all others (componentwise). None if the values are incomparable. */
fun minIn[s: Signal, p: TimeInterval]: lone Quantity {
  { v: measurementsIn[s, p].value | all w: measurementsIn[s, p].value | lte[v.byUnit, w.byUnit] }
}
/** MAX — the period value ≥ all others (componentwise). None if incomparable. */
fun maxIn[s: Signal, p: TimeInterval]: lone Quantity {
  { v: measurementsIn[s, p].value | all w: measurementsIn[s, p].value | lte[w.byUnit, v.byUnit] }
}

// ── SUM (FLOW/DISCRETE temporal total) via the parameterized keyed Σ-along-order fold ──────────────
// The keyed_sum[Measurement] Fold is pinned to the measurements: `val` = each measurement's value, and
// `earlier` = the same-signal time predecessor (tprev). keyed_sum's running total `cum` then folds the
// signal's values; the period SUM is the sub-chain total (rangeSum) of the period's first..last sample.

/** tprev — the immediate same-signal time-predecessor of `m` (lone). */
fun tprev[m: Measurement]: lone Measurement {
  { p: Measurement | p.of = m.of and earlierThan[p.at, m.at]
      and no q: Measurement | q.of = m.of and earlierThan[p.at, q.at] and earlierThan[q.at, m.at] }
}

/** MeasurementFold — pin the keyed_sum[Measurement] fold to the measurement history: each measurement's
    value and the per-signal time chain. (`cum` is then derived by keyed_sum's recurrence.) */
fact MeasurementFold {
  all m: Measurement | Fold.val[m] = m.value.byUnit
  all m: Measurement | let pr = tprev[m] |
    (some pr => Fold.earlier[m] = pr else no Fold.earlier[m])
}

/** SUM — the keyed Σ of a period's values, via `rangeSum` over the signal's time-ordered measurements.
    Returns the raw keyed map (NOT a Quantity atom: a fresh total need not equal any sampled value, and
    keyed_sum's raw-map fold avoids the value-object existence trap). */
fun sumIn[s: Signal, p: TimeInterval]: univ -> lone Scalar {
  let ms = measurementsIn[s, p] |
    (no ms => zero else rangeSum[firstIn[s, p], latestIn[s, p]])
}

/** metricResult — a Metric's value for a Quantity signal: LAST/FIRST/MIN/MAX (lone Quantity). (COUNT is
    an Int — use `countIn`; SUM is the keyed map `sumIn`, not a Quantity atom; MEAN is deferred.) */
fun metricResult[m: Metric]: lone Quantity {
  m.stat = LAST  => lastValueIn[m.observes, m.over]
  else m.stat = FIRST => firstValueIn[m.observes, m.over]
  else m.stat = MIN  => minIn[m.observes, m.over]
  else m.stat = MAX  => maxIn[m.observes, m.over]
  else none
}
