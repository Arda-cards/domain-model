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

// ── the spine adoptions ─────────────────────────────────────────────────────────────────────────
fact BaChain { balog/chained }
fact BaCommitPolicy { balog/commitAlwaysAccepts }

// ── reason-precise admission (the witnessing idiom) ─────────────────────────────────────────────
/** createBaViol — Create refuses only an already-created subject. */
fun createBaViol[o: CreateBaOcc]: set Reason { (some o.pre => RBaExists else none) }
/** baMutateViol — Update/Delete refuse an uncreated or retired subject. */
fun baMutateViol[o: BaOcc]: set Reason {
  ((no o.pre) => RBaNotCreated else none)
  + ((some o.pre and (o.pre & BusinessAffiliateState).sStatus = RD_RETIRED) => RBaRetired else none)
}

fact BaAdmissionWitnessed {
  all o: CreateBaOcc | (o.admission = Accepted iff no createBaViol[o]) and (o.admission in Rejected implies o.admission.because = createBaViol[o])
  all o: UpdateBaOcc | (o.admission = Accepted iff no baMutateViol[o]) and (o.admission in Rejected implies o.admission.because = baMutateViol[o])
  all o: DeleteBaOcc | (o.admission = Accepted iff no baMutateViol[o]) and (o.admission in Rejected implies o.admission.because = baMutateViol[o])
}

// ── effects (SET semantics on the write kinds; Delete carries content forward) ─────────────────
fact BaEffects {
  all o: BaWriteOcc | committed[o] implies {
    (o.post & BusinessAffiliateState).sStatus = RD_LIVE
    o.post.sRoles  = o.roles
  }
  all o: DeleteBaOcc | committed[o] implies {
    (o.post & BusinessAffiliateState).sStatus = RD_RETIRED
    o.post.sRoles  = o.pre.sRoles
  }
}

// ── the content axiom (C1 — see the contracts header for why this is a fact) ───────────────────
fact BaContentLaws { roleOwnership }
