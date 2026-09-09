module reference_data/business_affiliate/business_affiliate_implementation

/*
 * BUSINESS AFFILIATE — IMPLEMENTATION (DT-017). Integration roots open this file to get the
 * REAL module.
 *
 * Since the DT-023 cut 7b log conversion the module is NO LONGER static-degenerate: the
 * lifecycle machinery (chaining, reason-precise admission, effects) lives here, and the
 * contract's lifecycle laws are THEOREMS of it (proven in tests/business_affiliate.als).
 * The CONTENT law (role ownership — C1) remains an asserted axiom.
 */

open reference_data/business_affiliate/business_affiliate_contracts
open reference_data/business_affiliate/business_affiliate_types as bat   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[bat/BusinessAffiliate, bat/BusinessAffiliateState] as balog  // same params ⇒ the SAME spine instance
open meta/subject_log/lifecycle[bat/BusinessAffiliate, bat/BusinessAffiliateState] as lc      // same params ⇒ the SAME shapes instance

// ── the spine adoptions ─────────────────────────────────────────────────────────────────────────
fact BaChain { balog/chained }
fact BaCommitPolicy { balog/commitAlwaysAccepts }

// ── reason-precise admission (the witnessing idiom) ─────────────────────────────────────────────
/** createBaViol — Create refuses only an already-created subject (the generic create arm, the module's atom). */
fun createBaViol[o: CreateBaOcc]: set Reason { lc/createViol[o, RBaExists] }
/** baMutateViol — Update/Retire refuse an uncreated or already-retired subject (the generic liveness
    conditions; the module's two atoms — the closed atom split in two). */
fun baMutateViol[o: BaOcc]: set Reason {
  ((not lc/startedBefore[o]) => RBaNotCreated else none)
  + (lc/retiredBefore[o] => RBaRetired else none)
}

fact BaAdmissionWitnessed {
  all o: CreateBaOcc | (o.admission = Accepted iff no createBaViol[o]) and (o.admission in Rejected implies o.admission.because = createBaViol[o])
  all o: UpdateBaOcc | (o.admission = Accepted iff no baMutateViol[o]) and (o.admission in Rejected implies o.admission.because = baMutateViol[o])
  all o: RetireBaOcc | (o.admission = Accepted iff no baMutateViol[o]) and (o.admission in Rejected implies o.admission.because = baMutateViol[o])
}

// ── effects (SET semantics on the write kinds; the retire's tombstone is the lifecycle module's `RetireEffect`) ──
fact BaEffects {
  all o: BaWriteOcc | committed[o] implies o.post.sRoles = o.roles
}

// ── the content axiom (C1 — see the contracts header for why this is a fact) ───────────────────
fact BaContentLaws { roleOwnership }
