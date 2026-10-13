module reference_data/shared/tests/shared

open meta/kernel
open reference_data/item/item_implementation
open reference_data/business_affiliate/business_affiliate_implementation


// reference_data/shared — the DOMAIN-level shared module (the meta-equivalent at domain scope): holds
// cross-module verifications (and any domain-shared super-classes, when they arise) that belong to no
// single module. Here: the reference chain Item → ItemSupply → vendor PIN → BusinessRole(VENDOR)
// within a BusinessAffiliate VERSION, which spans the item and business_affiliate modules.
// DT-023 cut 7b: the chain's middle is the pin + role-selector pair (the SupplierReference handle
// DISSOLVED); resolution reads became version reads — dangling is unrepresentable by typing.

// A fully-linked single-tenant instance exists — the whole chain is satisfiable (not over-constrained).
pred coherent {
  some i: Item, s: ItemSupply, r: BusinessRole |
    s in itemSuppliesOf[i]   // version-carried since DT-023 cut 7a (the supply rides i's log)
    and s.supplierRole = r and r.role = VENDOR
    and i.tenantId = s.supplierPin.subject.tenantId
}
run unit_shared_coherent { coherent } for 6 but 2 RoleDetail, 5 Tick, 5 Snapshot, 5 Occurrence expect 1

// A present role selector is always a VENDOR role OF THE PINNED VERSION — UNSAT = holds
// (supplierPinsSound regression, the dissolved form of supplierIsVendor).
check unit_shared_supplierIsVendor {
  all s: ItemSupply | some s.supplierRole implies
    (s.supplierRole in s.supplierPin.post.sRoles and s.supplierRole.role = VENDOR)
} for 6 but 2 RoleDetail, 5 Tick, 5 Snapshot, 5 Occurrence expect 0

// Cross-tenant isolation over every resolved reference (kernel CrossTenantIsolation regression) — UNSAT.
// `some b` guard: an EMPTY resolve satisfies `b in Scoped` (subset), so the unguarded form is
// falsified by any dangling ref — same empty-set bug as the 2026-07-01 kernel fix.
check unit_shared_tenantIsolation {
  all a: Scoped, id: a.refs | let b = resolve[id] |
    (some b and b in Scoped) implies a.tenantId = b.tenantId
} for 6 but 2 RoleDetail, 5 Tick, 5 Snapshot, 5 Occurrence expect 0

// Negative: no ItemSupply's vendor pin reaches an affiliate in a different tenant — UNSAT
// (the pin-tenancy clause of supplierPinsSound).
run unit_shared_noCrossTenantSupplier {
  some s: ItemSupply |
    some s.supplierPin and s.supplierPin.subject.tenantId != s.tenantId
} for 6 but 2 RoleDetail, 5 Tick, 5 Snapshot, 5 Occurrence expect 0

// ── the named happy-path witnesses (unwitnessed-scenarios follow-up, 2026-07-08) ────────────────
// Previously covered only implicitly by the joint-SAT load; named so the shapes cannot silently
// die (the vacuous-witness lesson: a witness must EXCLUDE the degenerate satisfactions).

// The CLEAN read, pin form: a fully-LINKED supply row — pin AND selector present, the selector a
// role of the pinned version, same tenant — and NO half-linked row anywhere in the instance
// (the negative conjunct: every pinned row also selects its role).
run unit_shared_cleanResolution {
  some s: ItemSupply, r: BusinessRole | {
    s.supplierRole = r
    r in s.supplierPin.post.sRoles and r.role = VENDOR
    s.tenantId = s.supplierPin.subject.tenantId
  }
  all s: ItemSupply | some s.supplierPin implies some s.supplierRole
} for 6 but 2 RoleDetail, 5 Tick, 5 Snapshot, 5 Occurrence expect 1

// The linked-VENDOR selection is PRECISE, not incidental: the pinned VERSION bears MORE THAN
// ONE role, and the selector picks exactly its VENDOR one.
run unit_shared_linkedVendorPrecise {
  some s: ItemSupply, disj r1, r2: BusinessRole | {
    r1 in s.supplierPin.post.sRoles and r2 in s.supplierPin.post.sRoles
    r1.role = VENDOR and r2.role != VENDOR
    s.supplierRole = r1
  }
} for 6 but 2 RoleDetail, 5 Tick, 5 Snapshot, 5 Occurrence expect 1
