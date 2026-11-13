module meta/tests/kernel
// Reflects dafny-domain src/meta/tests/kernel-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/kernel

// The eId key constraint holds (sanity regression guard for EntityIdIsKey).
assert unit_kernel_eIdIsKey { all disj a, b: Entity | a.eId != b.eId }
check unit_kernel_eIdIsKey for 6 expect 0

// The kernel loads / is not over-constrained.
run unit_kernel_loads {} for 3 expect 1

// Isolation does not collapse the model to one tenant: two tenants' entities coexist,
// with an in-tenant data reference resolving. (Non-vacuity witness for CrossTenantIsolation.)
run unit_kernel_multiTenantLoads {
  some disj a, b: Scoped | a.tenantId != b.tenantId
  some a: Scoped, id: a.dataRefs | some resolve[id]
} for 5 expect 1

// A cross-tenant data reference is impossible (guard-rejection idiom: CrossTenantIsolation forbids it).
run unit_kernel_crossTenantRefImpossible {
  some disj a, b: Scoped | a.tenantId != b.tenantId and b.eId in a.dataRefs
} for 5 expect 0

// The 'soft' case stays representable: a dangling (unresolved / cross-Universe) reference is allowed.
run unit_kernel_danglingRefAllowed {
  some a: Entity, id: a.dataRefs | no resolve[id]
} for 4 expect 1

// An orphan EntityId (neither an identity nor referenced) is impossible (NoOrphanEntityId).
run unit_kernel_orphanIdImpossible {
  some id: EntityId | id not in Entity.eId + Entity.refs
} for 4 expect 0
