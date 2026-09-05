module reference_data/business_affiliate/business_affiliate_contracts

/*
 * BUSINESS AFFILIATE — CONTRACTS (DT-017). The module's laws as NAMED predicates: everything
 * a consumer may rely on, and nothing else. types + contracts = the DOMAIN statement.
 *
 * Since the DT-023 cut 7b log conversion the laws split by NATURE (the item precedent):
 *  - CONTENT laws (role ownership) remain AXIOMS — nothing deeper derives them; the
 *    implementation asserts them as facts (the degenerate-form heritage, now content-only).
 *  - LIFECYCLE laws (Create-first, retirement-terminal) are THEOREMS of the guards + effects,
 *    proven in the suite (check, UNSAT = holds) and assumable by consumers via the mock.
 *  - The CHAINING law is the spine's, adopted as fact and re-published here so consumer unit
 *    roots get the log shape from the mock.
 */

open reference_data/business_affiliate/business_affiliate_types as bat
open meta/subject_log/subject_log[bat/BusinessAffiliate, bat/BusinessAffiliateState] as balog  // same params ⇒ the SAME spine instance

// ── C1: role ownership (versioned — DT-023 Q-C folding) ─────────────────────────────────────────
/** Every BusinessRole belongs to exactly one affiliate's history and inherits its tenant.
    Consumers may navigate a version's sRoles as a strict in-tenant set. */
pred roleOwnership {
  all r: BusinessRole | one b: BusinessAffiliate | r in baRolesOf[b]
  all b: BusinessAffiliate, r: baRolesOf[b] | r.tenantId = b.tenantId
}
/** baRolesOf — every role appearing anywhere in `b`'s history (payloads + records). */
fun baRolesOf[b: BusinessAffiliate]: set BusinessRole {
  let os = { o: BaOcc | o.subject = b } | os.post.sRoles + (os & BaWriteOcc).roles
}

// ── C2: the lifecycle shape (DT-023 R1 — theorem of guards + effects) ──────────────────────────
/** A committed first occurrence on an affiliate is its Create (and Creates are only ever
    first); retirement is TERMINAL — nothing commits after the affiliate's state is Retired. */
pred baLifecycleShape {
  all o: BaOcc | committed[o] implies {
    ((no balog/priorOn[o]) iff o in CreateBaOcc)
    (some balog/priorOn[o] implies (balog/priorOn[o].post & BusinessAffiliateState).sStatus = RD_LIVE)
  }
}

// ── C3: the log is chained (the spine's law, re-published for mock consumers) ──────────────────
/** Every affiliate occurrence — refusals included — reads the real current record. */
pred baLogChained { balog/chained }

// ── the promise ──────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws. */
pred guarantees { roleOwnership and baLifecycleShape and baLogChained }
