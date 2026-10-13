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

/** baKindViol — a write that states a role version whose kind differs from its identity's refuses with
    `RRoleKindFixed` (R02-D24.1: a role's kind is fixed at birth). */
fun baKindViol[o: BaWriteOcc]: set Reason { (some v: o.roleVersions | v.vKind != v.of.role) => RRoleKindFixed else none }
/** baUpdateViol — Update refuses what the lifecycle refuses, and a change of a role's kind. */
fun baUpdateViol[o: UpdateBaOcc]: set Reason { baMutateViol[o] + baKindViol[o] }

fact BaAdmissionWitnessed {
  all o: CreateBaOcc | (o.admission = Accepted iff no createBaViol[o]) and (o.admission in Rejected implies o.admission.because = createBaViol[o])
  all o: UpdateBaOcc | (o.admission = Accepted iff no baUpdateViol[o]) and (o.admission in Rejected implies o.admission.because = baUpdateViol[o])
  all o: RetireBaOcc | (o.admission = Accepted iff no baMutateViol[o]) and (o.admission in Rejected implies o.admission.because = baMutateViol[o])
}

// ── effects (SET semantics on the write kinds; the retire's tombstone is the lifecycle module's `RetireEffect`) ──
fact BaEffects {
  all o: BaWriteOcc | committed[o] implies o.post.sRoleVersions = o.roleVersions   // the state holds exactly the versions written (R02-D24.1 review)
}

// ── a Create states each role at its birth kind (R02-D24.1) ────────────────────────────────────
// The identity is born with the kind the Create states; the runtime cannot produce a Create whose kind
// differs from the role it creates, so this is a well-formedness fact, not a refusal.
// A write states at most one version per role identity (R02-D24.1 review): a role appears once in the membership it sets.
fact BaWriteOneVersionPerRole { all o: BaWriteOcc | no disj v1, v2: o.roleVersions | v1.of = v2.of }
fact BaBirthStatesKind { all o: CreateBaOcc, v: o.roleVersions | v.vKind = v.of.role }

// ── the content axiom (C1 — see the contracts header for why this is a fact) ───────────────────
fact BaContentLaws { roleOwnership }
