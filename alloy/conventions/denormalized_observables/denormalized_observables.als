module conventions/denormalized_observables/denormalized_observables

/*
 * CONVENTION EXEMPLAR — DENORMALIZED OBSERVABLES (stored incremental values).
 * Canon: domain-log-kit §denormalized-observables (promoted from DT-018 F9).
 *
 * THE CONVENTION: when a needed reading is a SUM the solver cannot carry (the arity-4
 * ceiling — keyed folds fix ~250 atoms into every universe, past Kodkod's ~215 limit — is
 * the PERFORMANCE CANARY: an unmodelable sum usually means a runtime multi-join/group-by),
 * the value is STORED on the record and maintained INCREMENTALLY by occurrence effects —
 * pairwise (`post = pre + qty`), never a fold. This is NOT the mutable-counter anti-pattern:
 * the stored value never floats free — every change is a law-bound effect of a committed
 * occurrence, and the log remains the drill-down that can recompute it. The completeness
 * reading ("the stored value equals the recompute") is a THEOREM of the pairwise effect +
 * genesis + framing, stated CASE-WISE (0/1/2 exact) and discharged in a confined/dedicated
 * root — a solver-budget artifact, not a domain rule.
 *
 * THE EXEMPLAR: a Tally whose stored total accrues by Add postings. The cone is meta+shared
 * only, so even here the case-wise form is used — fidelity to the convention as practiced.
 */

open meta/profiles/domain_log                 // log anatomy + the group/order premises (P1)
open meta/kernel
open shared/values                            // Quantity (keyed), add over Unit -> lone Scalar
open meta/subject_log/subject_log[Tally, TallyRec] as tlog

// ── the subject ─────────────────────────────────────────────────────────────────────────────────
sig Tally extends Scoped {}
fact TallyRefs { all t: Tally | no t.dataRefs }

/** TallyRec — `total` is THE denormalized observable: stored, incrementally maintained. */
sig TallyRec extends Snapshot { total: lone Quantity }   // none = the keyed zero
fact TallyRecExtensional { all disj a, b: TallyRec | a.total != b.total }

sig OpenTallyOcc extends tlog/SubjectOcc {} { bindings = subject }
/** Add — the posting; ITS EFFECT is the only writer of `total`, and it is PAIRWISE. */
sig AddOcc extends tlog/SubjectOcc { qty: one Quantity } { bindings = subject + qty }

/** qtyMap — a lone Quantity as its keyed map (none = the keyed zero; the kit's encoding). */
fun qtyMap[q: Quantity]: Unit -> lone Scalar { q.byUnit }

// ── reason-precise admission (minimal) ──────────────────────────────────────────────────────────
one sig RAlreadyStarted, RNotStarted extends Reason {}
pred startedBeforeT[o: tlog/SubjectOcc] {
  some b: tlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
fun openViol[o: OpenTallyOcc]: set Reason { startedBeforeT[o] => RAlreadyStarted else none }
fun addViol[o: AddOcc]: set Reason { (not startedBeforeT[o]) => RNotStarted else none }
fact AdmissionWitness {
  all o: OpenTallyOcc | (o.admission = Accepted iff no openViol[o]) and (o.admission in Rejected implies o.admission.because = openViol[o])
  all o: AddOcc       | (o.admission = Accepted iff no addViol[o])  and (o.admission in Rejected implies o.admission.because = addViol[o])
}

// ── spine adoption + effects ────────────────────────────────────────────────────────────────────
fact TallyChain { tlog/chained }

fun tPre [o: tlog/SubjectOcc]: lone TallyRec { o.pre  & TallyRec }
fun tPost[o: tlog/SubjectOcc]: lone TallyRec { o.post & TallyRec }

fact EffectWitness {
  all o: OpenTallyOcc | committed[o] implies no tPost[o].total        // genesis = the keyed zero
  all o: AddOcc | committed[o] implies
    qtyMap[tPost[o].total] = add[qtyMap[tPre[o].total], qtyMap[o.qty]]   // PAIRWISE — no fold anywhere
}

// ── reads ───────────────────────────────────────────────────────────────────────────────────────
fun totalAt[t: Tally, k: Tick]: Unit -> lone Scalar { qtyMap[tlog/recordAt[t, k].total] }
/** startedTallyAt — spine read exported by name (module aliases are file-local). */
pred startedTallyAt[t: Tally, k: Tick] { tlog/startedAt[t, k] }
fun postingsUpTo[t: Tally, k: Tick]: set AddOcc {
  { o: AddOcc | committed[o] and o.subject = t and notAfter[o.tick, k] }
}

// ── the convention's laws ───────────────────────────────────────────────────────────────────────
/** accrues — the INCREMENTAL-EFFECT law: a committed posting changes the stored value by
    exactly its quantity (pairwise); this plus genesis + framing DEFINES the value for any
    number of postings by induction — no fold is ever stated. */
pred accrues {
  all o: AddOcc | committed[o] implies
    qtyMap[tPost[o].total] = add[qtyMap[tPre[o].total], qtyMap[o.qty]]
}

/** totalIsAccumulated — the COMPLETENESS reading (kit obligation (a)): the stored value
    equals the recompute over the log — a THEOREM of accrues, stated CASE-WISE (0/1/2 exact;
    dedicated-root scopes stay ≤ 2 postings). The general fold deliberately does not exist:
    at scale it cannot ride the cone (the arity-4 canary), and the runtime recomputes without
    ceilings (the probe's drill-down). */
pred totalIsAccumulated[t: Tally, k: Tick] {
  tlog/startedAt[t, k] implies {
    let ps = postingsUpTo[t, k] | {
      (no ps)   implies no totalAt[t, k]
      (one ps)  implies totalAt[t, k] = qtyMap[ps.qty]
      (#ps = 2) implies (some disj p1, p2: ps |
        totalAt[t, k] = add[qtyMap[p1.qty], qtyMap[p2.qty]])
    }
  }
}

/** guarantees — the exemplar's promise (the completeness reading is CHECKED in the root,
    not assumed). */
pred guarantees { accrues }
