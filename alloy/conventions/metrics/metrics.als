module conventions/metrics/metrics

/*
 * CONVENTION EXEMPLAR — METRICS (the read side; DT-007/DT-008).
 * Canon: metrics live NEXT TO the entities they measure and are PURE READS — as-of
 * projections over the logs, computed at a SAMPLING instant. No metric state is ever
 * stored, no occurrence ever writes a metric: the log is the only truth and the metric is a
 * function of it. (Contrast the denormalized_observables exemplar: THAT is what you build
 * when the reading must be stored; THIS is what you build when it need not be.)
 *
 * THE EXEMPLAR: Meters carry a set-able reading on their logs; the CELL is the Σ of all
 * meters' as-of values at the sampling instant, via a REAL keyed_sum fold — affordable here
 * because the conventions cone is meta+shared only (the core metrics cone lives at the
 * arity-4 ceiling; this file doubles as the fold-pinning recipe the kit points at, DT-013
 * F2). Two headline properties:
 *   - THE DT-008 BRIDGE: over a single meter, the cell ≡ the meter's ordinary state read
 *     (valueAt ≡ stateAsOf) — the metric adds machinery, never new truth.
 *   - SAMPLING IS AS-OF: readings set AFTER the sampling instant do not move the cell —
 *     the metric is a function of (logs, instant), not of "now".
 */

open meta/profiles/domain_log
open meta/kernel
open shared/values
open meta/subject_log/subject_log[Meter, MeterRec] as mlog2
open meta/keyed_value_algebra/keyed_sum[Meter] as msum

// ── the measured subjects ───────────────────────────────────────────────────────────────────────
sig Meter extends Scoped {}
fact MeterRefs { all m: Meter | no m.dataRefs }

sig MeterRec extends Snapshot { mVal: lone Quantity }
fact MeterRecExtensional { all disj a, b: MeterRec | a.mVal != b.mVal }

sig InstallMeterOcc extends mlog2/SubjectOcc {} { bindings = subject }
sig SetOcc extends mlog2/SubjectOcc { qty: one Quantity } { bindings = subject + qty }

fun qtyMap[q: Quantity]: Unit -> lone Scalar { q.byUnit }

// ── admission + effects (minimal) ───────────────────────────────────────────────────────────────
one sig RAlreadyStarted, RNotStarted extends Reason {}
pred startedBeforeM2[o: mlog2/SubjectOcc] {
  some b: mlog2/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
fun installViol[o: InstallMeterOcc]: set Reason { startedBeforeM2[o] => RAlreadyStarted else none }
fun setViol[o: SetOcc]: set Reason { (not startedBeforeM2[o]) => RNotStarted else none }
fact AdmissionWitness {
  all o: InstallMeterOcc | (o.admission = Accepted iff no installViol[o]) and (o.admission in Rejected implies o.admission.because = installViol[o])
  all o: SetOcc          | (o.admission = Accepted iff no setViol[o])     and (o.admission in Rejected implies o.admission.because = setViol[o])
}

fact MeterChain { mlog2/chained }
fun mPre2 [o: mlog2/SubjectOcc]: lone MeterRec { o.pre  & MeterRec }
fun mPost2[o: mlog2/SubjectOcc]: lone MeterRec { o.post & MeterRec }
fact EffectWitness {
  all o: InstallMeterOcc | committed[o] implies no mPost2[o].mVal
  all o: SetOcc          | committed[o] implies mPost2[o].mVal = o.qty   // SET (LOCF carries it)
}

// ── the ordinary state read (what the metric must AGREE with — DT-008) ──────────────────────────
fun meterValAt[m: Meter, t: Tick]: Unit -> lone Scalar { qtyMap[mlog2/recordAt[m, t].mVal] }
pred meterStartedAt[m: Meter, t: Tick] { mlog2/startedAt[m, t] }

// ── THE METRIC: a cell = Σ over meters, AS-OF the sampling instant ──────────────────────────────
/** Sample — THE sampling instant (the toy's period boundary; core: endOfPeriod ticks). */
one sig Sample { at: one Tick }

// The fold-pinning recipe (DT-013 F2 — copy this shape): `val` = each node's AS-OF value at
// the sampling instant; `earlier` = any linear chain over the nodes (the order is irrelevant
// to the result — add is commutative/associative under the ring premises).
fact FoldPinned {
  all m: Meter | msum/Fold.val[m] = meterValAt[m, Sample.at]
  all disj a, b: Meter | (a in b.^(msum/Fold.earlier)) or (b in a.^(msum/Fold.earlier))
}

/** cell — THE METRIC READ: the Σ of every meter's as-of value at the sampling instant.
    Pure function of (logs, instant); nothing anywhere writes it. */
fun cell: Unit -> lone Scalar { some Meter => msum/chainSum[Meter] else (none -> none & Unit -> Scalar) }

// ── the convention's laws ───────────────────────────────────────────────────────────────────────
/** cellBridgesToState — THE DT-008 BRIDGE: with a SINGLE meter, the metric read IS the
    ordinary state read (valueAt ≡ stateAsOf) — machinery adds no truth. */
pred cellBridgesToState {
  one Meter implies cell = meterValAt[Meter, Sample.at]
}

/** guarantees */
pred guarantees { cellBridgesToState }
