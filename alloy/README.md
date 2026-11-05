# Manufacturing Domain Model — `alloy/`

Alloy model of the manufacturing domain — the behavioral / model-finding model,
grounded in the public standard ontologies cached for reference in `../owl/`
(BFO/IOF/QUDT — source-of-truth, not maintained here). The directory tree mirrors the
system's **functional decomposition** (domain → directory, module → file), with a
non-domain `meta/` for modeling machinery. See `CLAUDE.md` for the full
conventions.

## Layout

```
alloy/
├── meta/           kernel.als · std/{bfo,qudt}.als (vendored stubs) · util.als · tests/
├── reference_data/ item.als                                    (+ tests/)
├── resources/      station · operator · loop · kanban_card · job · inventory_item   (+ tests/)
├── system/ procurement/ shop_access/ fulfillment/ operations/ receiving/ shipping/ oam/ workflows_and_integrations/   (stubbed)
└── tests/system.als
```

Module/dir names are **snake_case** (Alloy module names cannot contain `-` or
`.`), even though the functional domain canonical names are kebab-case
(`reference-data` ↔ `reference_data`).

## How to run

Use the repo-root **Makefile**:

```
make tools          # fetch Alloy + ROBOT (pinned)
make check-alloy    # run every command in every alloy/**/tests/*.als
make test-unit      # only unit_* commands
make test-sys       # the whole-system suite
make alloy          # launch the GUI — then File→Open a ROOT (a tests/*.als file)
```

Open a **root** (a `tests/*.als` file) in the Analyzer, never a library module —
commands only run from the opened root. Current roots:
`meta/tests/util.als` (X731Consistency), `resources/tests/kanban.als`
(showSimulation + ops), `tests/system.als` (whole-model smoke).

## Status

Relocation of the original `kanban.als` + `resource.als` into this structure is
complete and verified (X731Consistency UNSAT; showSimulation SAT; sys_modelLoads
SAT). Predicate/command names were kept; the redesign to the documented domain
model (and populating `meta/kernel` + `meta/std`) is the next phase — see the
workbook notebook `domain-ontology` (DT-001, DT-002).
