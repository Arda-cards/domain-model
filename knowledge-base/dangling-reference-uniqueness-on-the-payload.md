# Uniqueness over a soft reference is checked on the PAYLOAD, outside the resolution nesting

**Symptom (R02-D12, PR #2, 2026-10-01/02):** the attached-once rule for kanban pools was written as
`all p: InventoryPool | lone { o: StartProcessingOcc | committed[o] and resolve[o.pool] = p }`, and the
guard's arm sat under `some p: resolve[o.pool] & InventoryPool | …`. Both held — and two committed
attaches naming the SAME UNRESOLVED pool id satisfied them vacuously (probe: SAT, SAT; the
resolved-pool control UNSAT). The runtime's V019 index is unique on the stored `s_pool` VALUE.

**Mechanism:** `resolve[id]: lone Entity` is empty for a dangling id (the kernel permits unresolved
`EntityId`s deliberately — `NoOrphanEntityId` only forbids ids nobody bears or names). A law quantified
over the resolved entity, or an arm nested under `some p: resolve[…]`, says nothing about occurrences
whose reference does not resolve: the "at most one" is over `InventoryPool` atoms, not over the ids
the occurrences carry. Any uniqueness the runtime enforces on a stored column is a statement about
the payload, and the model's form must be too.

**Rule:** state column-uniqueness over the id and compare payloads directly —
`all e: EntityId | lone { o: StartProcessingOcc | committed[o] and o.pool = e }`, and in the arm
`some s: StartProcessingOcc - o | committed[s] and s.pool = o.pool and precedes[s.tick, o.tick]`
OUTSIDE the `some p: resolve[o.pool]` nesting (`kanban_card_contracts.als`,
`kanban_card_implementation.als`). Only clauses that genuinely need the entity (a membership row on the
pool, its tenant, its item) stay under the resolution.

**Test shape:** a RED-first witness per vacuity — two committed occurrences with one unresolved id
(`s1.pool = s2.pool and no resolve[s1.pool]`) expected refused/UNSAT — plus the resolved-pool control
kept, so the measurement can fail (`tests/cycle_retire.als`, `unit_cyr_*DanglingId*`,
`unit_cyr_attachedOnceById`). A witness that compares `resolve[a] = resolve[b]` is satisfiable by two
DIFFERENT dangling ids; compare `a = b`.
