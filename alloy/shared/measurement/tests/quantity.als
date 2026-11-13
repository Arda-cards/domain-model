module shared/measurement/tests/quantity
// Reflects dafny-domain src/shared/measurement/tests/quantity-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

/*
 * Tests for the V=Quantity instantiation: MIN/MAX (keyed partial order) and the metricResult dispatch.
 * Under the keyed_order premise (ringAxioms + orderAxioms) so the algebra is meaningful, like the
 * inventory_item tests. (Temporal SUM is deferred — see quantity.als.)
 */

open shared/measurement/quantity

fact ScalarPremises { groupAxioms and orderAxioms }   // group suffices: domain roots do additive arithmetic only (DT-011)

// ── coherence (expect SAT) ────────────────────────────────────────────────────────────────
// A period with two comparable values: MIN and MAX both exist and are sampled values.
run unit_q_minMax {
  some s: Signal, p: TimeInterval |
    some minIn[s, p] and some maxIn[s, p]
    and minIn[s, p] in measurementsIn[s, p].value
    and maxIn[s, p] in measurementsIn[s, p].value
} for 5 but 3 Scalar expect 1

// A single-sample period: MIN = MAX = that value.
run unit_q_minMaxSingle {
  some s: Signal, p: TimeInterval, m: Measurement |
    measurementsIn[s, p] = m and minIn[s, p] = m.value and maxIn[s, p] = m.value
} for 5 but 3 Scalar expect 1

// metricResult dispatches LAST / MIN to the right selector.
run unit_q_dispatch {
  (some mt: Metric | mt.stat = LAST and metricResult[mt] = lastValueIn[mt.observes, mt.over])
  and (some mt: Metric | mt.stat = MIN and metricResult[mt] = minIn[mt.observes, mt.over])
} for 5 but 3 Scalar expect 1

// ── invariants (check; UNSAT = holds) ───────────────────────────────────────────────────────
// MIN ≤ MAX whenever both exist.
assert unit_q_minLeMax {
  all s: Signal, p: TimeInterval |
    (some minIn[s, p] and some maxIn[s, p]) implies lte[minIn[s, p].byUnit, maxIn[s, p].byUnit]
}
check unit_q_minLeMax for 5 but 3 Scalar expect 0

// MIN/MAX, when present, are actual sampled values of the period.
assert unit_q_minMaxSampled {
  all s: Signal, p: TimeInterval |
    (some minIn[s, p] implies minIn[s, p] in measurementsIn[s, p].value)
    and (some maxIn[s, p] implies maxIn[s, p] in measurementsIn[s, p].value)
}
check unit_q_minMaxSampled for 5 but 3 Scalar expect 0

// metricResult agrees with the generic LAST/FIRST selectors.
assert unit_q_dispatchLastFirst {
  all mt: Metric |
    (mt.stat = LAST implies metricResult[mt] = lastValueIn[mt.observes, mt.over])
    and (mt.stat = FIRST implies metricResult[mt] = firstValueIn[mt.observes, mt.over])
}
check unit_q_dispatchLastFirst for 5 but 3 Scalar expect 0

// ── SUM (temporal total via keyed_sum) ───────────────────────────────────────────────────────
// A period summing two different-UNIT single values widens to a 2-unit total (keyed Σ).
run unit_q_sumWidens {
  some s: Signal, p: TimeInterval, disj m1, m2: Measurement |
    m1.of = s and m2.of = s and m1 in measurementsIn[s, p] and m2 in measurementsIn[s, p]
    and isSingle[m1.value.byUnit] and isSingle[m2.value.byUnit]
    and m1.value.byUnit.Scalar != m2.value.byUnit.Scalar    // different units (keys)
    and isMulti[sumIn[s, p]]
} for 5 but 3 Scalar expect 1

// A single-sample period sums to that sample's value — UNSAT = holds.
assert unit_q_sumSingleton {
  all s: Signal, p: TimeInterval |
    one measurementsIn[s, p] implies sumIn[s, p] = (firstIn[s, p]).value.byUnit
}
check unit_q_sumSingleton for 5 but 3 Scalar expect 0
