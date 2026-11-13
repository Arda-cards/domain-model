module meta/kernel

/*
 * Modeling kernel: identity, the Entity bound, tenant scoping, soft-reference
 * resolution. Domain payloads extend Entity (or Scoped). Timeless — the bitemporal
 * axis is the runtime's, not the model's (RA-02, 2026-11-05; the meta/bitemporal stub left with TN-003 row 3). See modeling-conventions.
 */

/** EntityId — an opaque, globally-unique identity value. Alloy atoms are inherently
    distinct and `=` is identity equality, so each EntityId atom IS a unique identity. */
sig EntityId {}

/** Entity — an identity-bearing thing: the root of every domain object, with a
    primary-key `eId` (injective, EntityIdIsKey) and its OUTGOING soft references
    `dataRefs` (the complete set is the derived `refs`). */
// dataRefs excludes the scope ref; each concrete module pins it (`no x.dataRefs` when
// empty), since Alloy has no field reflection.
abstract sig Entity {
  eId:      one EntityId,
  dataRefs: set EntityId
}
fact EntityIdIsKey { all disj a, b: Entity | a.eId != b.eId }

/** Scoped — an Entity that belongs to (is partitioned by) a tenant, carried as the soft
    reference `tenantId` (an EntityId, not a Tenant sig, keeping the kernel domain-free). */
// The Tenant entity lives in the system domain (not yet modeled).
abstract sig Scoped extends Entity { tenantId: one EntityId }

// The COMPLETE set of an entity's outgoing soft references: the module-declared
// `dataRefs` PLUS, for a Scoped entity, its scope reference (`tenantId`).
// `this.tenantId` is empty for non-Scoped entities, so this holds for any Entity.
// Generic cross-reference rules quantify over `refs`.
fun Entity.refs: set EntityId { this.dataRefs + this.tenantId }

// Cross-tenant isolation — over the complete `refs` set, restricted to tenant-bearing
// entities: if a Scoped entity refers to another Scoped entity that resolves in
// scope, they share a tenant. Refs to non-Scoped/global entities (incl. the scope
// ref's Tenant), or unresolved refs, are exempt via the `some b and b in Scoped` guard.
// (`some b` is REQUIRED: `in` is subset, so an EMPTY resolve satisfies `b in Scoped`
// and would force `a.tenantId = none` — silently banning dangling refs. Bug found and
// fixed 2026-07-01; unit_kernel_danglingRefAllowed is the regression guard.)
fact CrossTenantIsolation {
  all a: Scoped, id: a.refs |
    let b = resolve[id] | (some b and b in Scoped) implies a.tenantId = b.tenantId
}

// Tight by default: no orphan identities — every EntityId is either some entity's
// own identity or is referenced by some entity. (Relax explicitly to model a
// minted-but-not-yet-used id.) See modeling-conventions §6.
fact NoOrphanEntityId { all id: EntityId | id in Entity.eId + Entity.refs }

// Resolve a soft reference within the current scope. `lone`: 0 (dangling /
// not-loaded / cross-Universe — the 'soft' case) or 1 (key ⇒ never more).
fun resolve[id: EntityId]: lone Entity { eId.id }
