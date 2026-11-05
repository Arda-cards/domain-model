module conventions/pinning_freezing/pinning_freezing

/*
 * CONVENTION EXEMPLAR — PINNING / FREEZING (reference forms: LIVE / PINNED / COPIED).
 * Canon: modeling-conventions §7 (+ §7.1 quasi-static scope, §7.2 the freeze obligation).
 *
 * THE TENSION: reference data stays EDITABLE while the documents that cite it must show WHAT
 * WAS TRUE at commitment time. The log/bitemporal substrate resolves it SYSTEMICALLY: records
 * are append-only and coordinate-addressed, so a reference can be read AS-OF any moment and a
 * particular coordinate can be PINNED forever.
 *
 * THE EXEMPLAR: a toy log-carried Vendor (renameable — the mutable reference target the core's
 * QUASI-STATIC modules deliberately don't have) and a toy Doc that COMMITS (freezes). The Doc
 * demonstrates all three forms against a GENUINELY MUTABLE target — the non-vacuous
 * demonstration the core models cannot exhibit:
 *   LIVE   — `dVendor` read as-of NOW: tracks renames (correct for operational reads;
 *            a de-facto freeze violation if used where frozen was intended — WITNESSED).
 *   COPIED — `dCopy`: the name VALUE captured at commit onto the Doc's OWN record, bound by
 *            the Doc's own frame law (the SupplierBinding / sItemData shape).
 *   PINNED — `dPinAt`: the commit COORDINATE carried on the record; the pinned read is
 *            ref + coordinate through the ordinary as-of machinery — no data copied.
 * The headline theorem: PIN and COPY agree forever; the headline witness: LIVE drifts.
 *
 * Both subjects share this file, so cross-subject reads are same-module/ATOMIC — the exemplar
 * isolates the reference-form idea from the cross-module consistency questions (those have
 * their own exemplars).
 */

open meta/profiles/domain_log                              // log anatomy premises (P1)
open meta/kernel                                           // Scoped, EntityId, resolve
open meta/subject_log/subject_log[Vendor, VendorRec] as vlog
open meta/subject_log/subject_log[Doc, DocRec] as dlog

// ── the mutable reference target ────────────────────────────────────────────────────────────────
sig Name {}
fact NoOrphanName { all n: Name | n in VendorRec.vName + RegisterOcc.name0 + RenameOcc.newName }

/** Vendor — the toy reference entity; log-carried so renames are REPRESENTABLE (the whole
    point: the core's quasi-static reference modules can't exhibit the drift this file shows). */
sig Vendor extends Scoped {}
fact VendorRefs { all v: Vendor | no v.dataRefs }

sig VendorRec extends Snapshot { vName: one Name }
fact VendorRecExtensional { all disj a, b: VendorRec | a.vName != b.vName }

/** Register — vendor genesis. */
sig RegisterOcc extends vlog/SubjectOcc { name0: one Name } { bindings = subject + name0 }
/** Rename — THE mutation the freeze must survive. */
sig RenameOcc extends vlog/SubjectOcc { newName: one Name } { bindings = subject + newName }

fun vendorNameAt[v: Vendor, t: Tick]: lone Name { vlog/recordAt[v, t].vName }

// ── the freezing document ───────────────────────────────────────────────────────────────────────
abstract sig DocStatus {}
one sig D_DRAFT, D_COMMITTED extends DocStatus {}

sig Doc extends Scoped {}
fact DocRefs { all d: Doc | no d.dataRefs }

/** DocRec — carries all THREE forms side by side (didactic; a real record picks per §7.2). */
sig DocRec extends Snapshot {
  dStatus: one  DocStatus,
  dVendor: one  EntityId,   // LIVE ref → Vendor (reads through it track renames)
  dCopy:   lone Name,       // COPIED at commit (none while DRAFT)
  dPinAt:  lone Tick        // PINNED commit coordinate (none while DRAFT)
}
fact DocRecExtensional {
  all disj a, b: DocRec |
    a.dStatus != b.dStatus or a.dVendor != b.dVendor or a.dCopy != b.dCopy or a.dPinAt != b.dPinAt
}
fact DocVendorTyped { all r: DocRec | let v = resolve[r.dVendor] | some v implies v in Vendor }

/** OpenDoc — doc genesis (DRAFT, live ref only). */
sig OpenDocOcc extends dlog/SubjectOcc { vendor: one EntityId } { bindings = subject + vendor }
/** CommitDoc — THE FREEZE INSTANT: captures the copy and the pin coordinate. */
sig CommitDocOcc extends dlog/SubjectOcc {} { bindings = subject }
/** TouchDoc — a post-commit no-op kind (post = pre), so the frozen fields' persistence is
    exercised by real occurrences rather than holding vacuously. */
sig TouchDocOcc extends dlog/SubjectOcc {} { bindings = subject }

// ── reads: the three forms ──────────────────────────────────────────────────────────────────────
fun docStateAt[d: Doc, t: Tick]: lone DocRec { dlog/recordAt[d, t] }
/** liveNameOf — the LIVE form: resolve now, read as-of `t`. */
fun liveNameOf[r: DocRec, t: Tick]: lone Name { vendorNameAt[resolve[r.dVendor] & Vendor, t] }
/** pinnedNameOf — the PINNED form: the SAME ref, the FROZEN coordinate. No data copied. */
fun pinnedNameOf[r: DocRec]: lone Name { vendorNameAt[resolve[r.dVendor] & Vendor, r.dPinAt] }

// ── reason-precise admission (minimal — see the reason_precise_refusals exemplar) ───────────────
one sig RAlreadyStarted, RNotStarted, RBadState extends Reason {}

pred startedBeforeV[o: vlog/SubjectOcc] {
  some b: vlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
pred startedBeforeD[o: dlog/SubjectOcc] {
  some b: dlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
fun registerViol[o: RegisterOcc]: set Reason { startedBeforeV[o] => RAlreadyStarted else none }
fun renameViol[o: RenameOcc]: set Reason { (not startedBeforeV[o]) => RNotStarted else none }
fun openViol[o: OpenDocOcc]: set Reason {
  (startedBeforeD[o] => RAlreadyStarted else none)
  + ((let v = resolve[o.vendor] & Vendor | no v or no vendorNameAt[v, o.tick]) => RBadState else none)
}
fun commitViol[o: CommitDocOcc]: set Reason {
  ((not startedBeforeD[o]) => RNotStarted else none)
  + ((startedBeforeD[o] and dPre[o].dStatus != D_DRAFT) => RBadState else none)
    // GUARDS READ o.pre — the chained record (never recordAt at o.tick: LOCF reads are
    // INCLUSIVE, so an occurrence would see its OWN post-state and refuse itself).
}
fun touchViol[o: TouchDocOcc]: set Reason { (not startedBeforeD[o]) => RNotStarted else none }

fact AdmissionWitness {
  all o: RegisterOcc  | (o.admission = Accepted iff no registerViol[o]) and (o.admission in Rejected implies o.admission.because = registerViol[o])
  all o: RenameOcc    | (o.admission = Accepted iff no renameViol[o])   and (o.admission in Rejected implies o.admission.because = renameViol[o])
  all o: OpenDocOcc   | (o.admission = Accepted iff no openViol[o])     and (o.admission in Rejected implies o.admission.because = openViol[o])
  all o: CommitDocOcc | (o.admission = Accepted iff no commitViol[o])   and (o.admission in Rejected implies o.admission.because = commitViol[o])
  all o: TouchDocOcc  | (o.admission = Accepted iff no touchViol[o])    and (o.admission in Rejected implies o.admission.because = touchViol[o])
}

// ── spine adoption + effects ────────────────────────────────────────────────────────────────────
fact VendorChain { vlog/chained }
fact DocChain    { dlog/chained }

fun vPost[o: vlog/SubjectOcc]: lone VendorRec { o.post & VendorRec }
fun dPre [o: dlog/SubjectOcc]: lone DocRec { o.pre  & DocRec }
fun dPost[o: dlog/SubjectOcc]: lone DocRec { o.post & DocRec }

fact EffectWitness {
  all o: RegisterOcc | committed[o] implies vPost[o].vName = o.name0
  all o: RenameOcc   | committed[o] implies vPost[o].vName = o.newName
  all o: OpenDocOcc | committed[o] implies {
    dPost[o].dStatus = D_DRAFT
    dPost[o].dVendor = o.vendor
    no dPost[o].dCopy and no dPost[o].dPinAt
  }
  all o: CommitDocOcc | committed[o] implies {
    dPost[o].dStatus = D_COMMITTED
    dPost[o].dVendor = dPre[o].dVendor
    dPost[o].dCopy  = liveNameOf[dPre[o], o.tick]   // THE COPY: the live read, captured once
    dPost[o].dPinAt = o.tick                        // THE PIN: the coordinate, carried
  }
  all o: TouchDocOcc | committed[o] implies o.post = o.pre
}

// ── the convention's laws ───────────────────────────────────────────────────────────────────────
/** committedDocAt — the doc stands COMMITTED (frozen) at `t`. */
pred committedDocAt[d: Doc, t: Tick] { docStateAt[d, t].dStatus = D_COMMITTED }

/** copyFrozen — the COPIED form's guarantee: from the commit on, the copy (and the pin
    coordinate) never change, no matter what happens to the vendor. */
pred copyFrozen {
  all d: Doc, t1, t2: Tick |
    (notAfter[t1, t2] and committedDocAt[d, t1]) implies {
      docStateAt[d, t2].dCopy  = docStateAt[d, t1].dCopy
      docStateAt[d, t2].dPinAt = docStateAt[d, t1].dPinAt
    }
}

/** pinAgreesWithCopy — the headline THEOREM: the pinned read (ref + frozen coordinate, no
    data copied) and the copy (data captured, no coordinate kept) denote the SAME name,
    forever — two implementations of one freeze semantics. */
pred pinAgreesWithCopy {
  all d: Doc, t: Tick | committedDocAt[d, t] implies
    pinnedNameOf[docStateAt[d, t]] = docStateAt[d, t].dCopy
}

/** guarantees — the exemplar's promise. */
pred guarantees { copyFrozen and pinAgreesWithCopy }
