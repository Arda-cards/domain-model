# A key that is no entity's identity gets its own sig

**The gotcha.** `meta/kernel.als` states `NoOrphanEntityId`: every `EntityId` atom is some entity's identity (`eId`) or a
reference some entity carries (`refs`). It keeps scopes tight. It also means that an `EntityId` field on something that is
NOT an entity, a value or an occurrence, can only hold ids that entities already use.

For a soft REFERENCE carried by a record or a row (a demand's holding, a start's pool) that is harmless: the id names an
entity, or it dangles and happens to coincide with some other id in use.

For a KEY it is wrong. A contribution's key (TN-004) identifies a value inside its demand and names no entity. Typed
`EntityId`, it could only be the demand's id, a pool's, a tenant's: whichever was in use. Nothing failed, because the laws
compare keys only with keys, but instances showed keys equal to unrelated entities' ids, and the number of distinct keys in
a history was silently capped by the number of ids in use. Copilot found it reviewing domain-model pull request 12.

**The rule.** A key that is not an entity's identity gets its own sig (`ContributionId` in
`operations/demand/demand_types.als`), as the inert values `Note` and `Reference` have theirs:

- the fields and the acts that carry the key take that type;
- every command of the cone pins it (`2 ContributionId`, or as many as one holder carries; gotcha 7 of `alloy/CLAUDE.md`);
- it needs no orphan fact. The Dafny reference model writes `type ContributionId = EntityId` and has no orphan rule, so
  a free key type is the faithful reading of that alias here.

**How to see the defect.** A finder that asks for a key outside `Entity.eId + Entity.refs`, with the comparison typed over
`univ` so that it still type-checks once the key has its own sig (`unit_dem_contributionKeyIsItsOwn`). It finds none while
the key is an `EntityId`.
