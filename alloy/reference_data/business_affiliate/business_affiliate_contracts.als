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
 *  - The ROLE-KIND law (C4, R02-D24.1: a role's kind is fixed at birth) is a THEOREM of the
 *    Update guard (`RRoleKindFixed`) and the Create fact, proven in the suite.
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
    (some balog/priorOn[o] implies balog/priorOn[o] not in RetireBaOcc)   // the prior head is never the tombstone (terminality)
  }
}

// ── C3: the log is chained (the spine's law, re-published for mock consumers) ──────────────────
/** Every affiliate occurrence — refusals included — reads the real current record. */
pred baLogChained { balog/chained }

// ── C4: a role's kind is fixed at birth (R02-D24.1 — theorem of the Update guard + the Create fact) ─
/** committedRoleVersion — `v` is stated by a committed write. */
pred committedRoleVersion[v: BusinessRoleVersion] { some o: BaWriteOcc | committed[o] and v in o.roleVersions }
/** Every committed role version states the kind its identity was born with: a role's kind never
    changes (replacing a role by a new identity of another kind is not a change of kind). */
pred roleKindFixedAtBirth { all v: BusinessRoleVersion | committedRoleVersion[v] implies v.vKind = v.of.role }

// ── the promise ──────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws. */
pred guarantees { roleOwnership and baLifecycleShape and baLogChained and roleKindFixedAtBirth }
