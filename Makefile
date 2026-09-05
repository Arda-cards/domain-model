# Manufacturing-ontologies — analysis tasks.
#
# Tools (Alloy, ROBOT) are fetched pinned + checksum-verified into tools/ by
# tools/get-tools.sh (reusing ~/tools when present). tools/*.jar is gitignored.
# Run targets from the repo root.

ALLOY := tools/alloy.jar
ROBOT := tools/robot.jar
# Extra flags for `alloy exec`. Default = glucose (JNI native in this jar; loads on darwin/arm64
# and is dramatically faster than SAT4J on this model — MP ruling 2026-07-17, DT-015 completion
# session). On a machine where the native fails to load, revert to pure-Java SAT4J with
# ALLOY_FLAGS='' (env or make arg — `?=` yields). Both are sound/complete: only speed differs.
ALLOY_FLAGS ?= -s glucose
# Alloy exec output (receipts + solution dumps) goes here — gitignored; never committed.
# `out/` is in .gitignore; wipe it with `make clean`.
OUT := out/alloy

.PHONY: tools alloy check-layering check-open-params check-alloy check-examples check-units check-integration test-unit test-sys soak soak-plan soak-chunk soak-status soak-harvest cnf-export report report-examples check clean

## tools: fetch/verify the pinned analysis tools (Alloy, ROBOT)
tools:
	@bash tools/get-tools.sh

$(ALLOY) $(ROBOT):
	@bash tools/get-tools.sh

## alloy: launch the Alloy Analyzer GUI (then File-Open a ROOT, e.g. alloy/resources/tests/kanban.als)
alloy: $(ALLOY)
	@java -jar $(ALLOY) &

# NOTE: commands carry `expect 1` (SAT) / `expect 0` (UNSAT); a result that does not match its
# `expect` makes the Alloy CLI return a non-zero exit. The recipes below capture that per-root exit
# code (a plain pipe would mask it) and fail the target on any mismatch — so a guard-rejection that
# silently flips to SAT, or a check that develops a counterexample, breaks the build.

## check-layering: enforce the DT-001.12 layer law — meta never opens shared; meta/shared never open a domain
DOMAIN_DIRS := system|reference_data|resources|procurement|shop_access|fulfillment|operations|receiving|shipping|oam|workflows_and_integrations
check-layering:
	@fail=0; \
	if grep -rn '^open shared/' alloy/meta --include='*.als'; then \
	  echo "FAIL: meta must not open shared (DT-001.12 layer law)"; fail=1; fi; \
	if grep -rnE '^open ($(DOMAIN_DIRS)|conventions)/' alloy/meta alloy/shared --include='*.als'; then \
	  echo "FAIL: meta/shared must not open a domain or conventions (DT-001.12 layer law)"; fail=1; fi; \
	if grep -rn '^open ' alloy/conventions --include='*.als' 2>/dev/null | grep -vE ':open (meta|shared|conventions)/'; then \
	  echo "FAIL: conventions exemplars may open meta/, shared/, or their own files ONLY (MP 2026-07-08)"; fail=1; fi; \
	if grep -rn '^open conventions/' alloy --include='*.als' | grep -v '^alloy/conventions/'; then \
	  echo "FAIL: only conventions/ files may open conventions/ (exemplars are not libraries — MP 2026-07-08)"; fail=1; fi; \
	if grep -rn '^open resources/inventory_item/legacy' alloy --include='*.als'; then \
	  echo "FAIL: nothing may open the archived legacy carrier (DT-011 — moved to alloy-sample/inventory_item_legacy)"; fail=1; fi; \
	if grep -rn '^open .*_mock' alloy --include='*.als' | grep -vE '/tests/|^alloy/soak/'; then \
	  echo "FAIL: only test/soak ROOTS may open a module mock (DT-017 — library files open peers' _types only; soak slices are command-carrying roots, DT-024)"; fail=1; fi; \
	for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*'); do \
	  for m in $$(grep -E '^open [a-z0-9_/]*_mock' "$$f" | awk '{print $$2}' | sed 's|_mock$$||'); do \
	    if grep -qE "^open $$m"_implementation "$$f"; then \
	      echo "FAIL: $$f opens both $${m}_mock and $${m}_implementation (DT-017 — meaningless universe)"; fail=1; fi; \
	  done; \
	done; \
	[ $$fail -eq 0 ] && echo "OK: layering respected (meta -/-> shared -/-> domains; DT-017 mock discipline)" || exit 1

## check-open-params: model-gate rule 10 — every parameter of a parametric `open` is alias-qualified or declared locally
##   (tools/open-params-gate.py; --selftest runs its 14 cases). Sibling: tools/adoption-gate.py (rule 9, adopted preds owe a check).
check-open-params:
	python3 tools/open-params-gate.py --selftest > /dev/null && python3 tools/open-params-gate.py alloy

## check-alloy: run every command in every test root (any alloy/**/tests/*.als); fail on expect mismatch.
## CHECK_SCOPE=alloy/<family> restricts the walk to one subtree — used by the full-gate CI workflow
## to shard the gate across matrix jobs; the default (whole tree) is the push gate, unchanged.
CHECK_SCOPE ?= alloy
check-alloy: $(ALLOY) check-layering
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find $(CHECK_SCOPE) -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec $(ALLOY_FLAGS) -c "*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect (see 'against expectation' above)"; exit 1; fi; \
	echo "OK: all commands matched their expect"

## check-affected: cone-aware incremental gate — run only roots whose open-cone touches changed files
## (scaling-outlook to-do #1). FILES="a.als b.als" overrides; default = git-changed alloy files.
## merge-plan: deterministic re-verification plan for a merge (model-merge gate, MP-5 protocol
## 2026-08-28). RANGE=a..b or FILES="..." ; prints tiers/roots/rungs, runs nothing.
merge-plan:
	@tools/merge-plan.sh $(if $(RANGE),RANGE=$(RANGE)) $(if $(FILES),FILES="$(FILES)")

check-affected: $(ALLOY) check-layering
	@files="$(FILES)"; \
	[ -z "$$files" ] && files="$$( (git diff --name-only HEAD -- alloy; git diff --cached --name-only -- alloy) | sort -u)"; \
	if [ -z "$$files" ]; then echo "check-affected: no changed alloy files — nothing to run"; exit 0; fi; \
	echo "changed:"; for c in $$files; do echo "  $$c"; done; \
	mkdir -p $(OUT); fail=0; ran=0; \
	for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' | sort); do \
	  cone="$$(tools/cone.sh $$f)"; hit=0; \
	  for c in $$files; do case "$$cone" in *"$$c"*) hit=1;; esac; done; \
	  [ $$hit -eq 1 ] || continue; ran=$$((ran+1)); echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec $(ALLOY_FLAGS) -c "*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	echo "affected roots run: $$ran"; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect"; exit 1; fi; \
	echo "OK: all affected commands matched their expect (NOT the full gate — run check-alloy before push)"

## check-alloy-par: the full gate fanned out across cores (scaling-outlook to-do #2); PAR=N workers
## (default 4 — each root is its own JVM). Per-root logs + instances under out/par/.
PAR ?= 4
check-alloy-par: $(ALLOY) check-layering
	@rm -rf out/par; mkdir -p out/par; \
	roots="$$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' | sort)"; \
	n=$$(echo "$$roots" | grep -c .); \
	echo "$$roots" | ALLOY_JAR=$(ALLOY) ALLOY_FLAGS='$(ALLOY_FLAGS)' xargs -P $(PAR) -n 1 tools/run-root.sh; \
	logs=$$(ls out/par/*.log 2>/dev/null | grep -c . || echo 0); \
	fail=0; \
	if [ "$$logs" != "$$n" ]; then echo "FAIL: expected $$n root logs, found $$logs (a runner died before logging)"; fail=1; fi; \
	for l in out/par/*.log; do \
	  [ -f "$$l" ] || continue; \
	  if ! grep -qE 'SAT|UNSAT' "$$l"; then echo "INCOMPLETE (no solver output): $$l"; fail=1; fi; \
	  if grep -qiE 'against expectation' "$$l"; then echo "MISMATCH in $$l:"; grep -iE 'against expectation' "$$l"; fail=1; fi; \
	  if grep -qE '\[main\] (ERROR|SEVERE)|Exception in thread' "$$l"; then echo "ERROR in $$l"; fail=1; fi; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: see out/par/*.log"; exit 1; fi; \
	echo "OK: all commands matched their expect ($$n roots, PAR=$(PAR))"

## check-budget: BEST-EFFORT universe-budget lint (scaling-outlook to-do #3) — per root, estimate
## the largest command universe (2^Int + explicit scope counts + one-sigs in the cone) and warn
## past the arity-4 folklore ceiling (~215 atoms). A heuristic: unscoped sigs at the `for N`
## default are NOT counted — treat warnings as real, silence as advisory only.
BUDGET ?= 215
check-budget:
	@for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' | sort); do \
	  ones=$$(tools/cone.sh $$f | xargs grep -hE '^one sig' 2>/dev/null | grep -oE 'one sig [A-Za-z0-9_, ]+' | sed 's/one sig //' | tr ',' '\n' | grep -c . || echo 0); \
	  max=$$(grep -hoE 'for [0-9]+( but [^{]*)?expect' "$$f" | sed 's/expect//' | \
	    awk -v ones="$$ones" '{ \
	      intv=0; sum=0; \
	      for (i=1; i<=NF; i++) { \
	        if ($$i ~ /^[0-9]+$$/) { n=$$i; nx=$$(i+1); \
	          if (nx == "Int" || nx == "Int,") intv=n; \
	          else if (i>1 && $$(i-1)=="for") next_default=n; \
	          else sum+=n; } } \
	      u = (intv>0 ? 2^intv : 0) + sum + ones; \
	      if (u>m) m=u } END { print m+0 }'); \
	  flag=""; [ "$$max" -gt $(BUDGET) ] && flag="  <-- WARN: past the ~$(BUDGET)-atom arity-4 ceiling (fine if the cone has no arity-4 relations)"; \
	  printf '%-70s max-est %5s%s\n' "$$f" "$$max" "$$flag"; \
	done

## check-examples: run every command in the modeling cookbook (alloy/meta/examples/*.als)
check-examples: $(ALLOY)
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy/meta/examples -name '*.als' ! -name 'ex00_*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec $(ALLOY_FLAGS) -c "*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect (see 'against expectation' above)"; exit 1; fi; \
	echo "OK: all commands matched their expect"

## check-units: the DEV-LOOP tier (DT-017) — every test root EXCEPT tests/integration/ (unit roots
## run this module's implementation against peers' MOCKS; minutes, run freely while developing)
check-units: $(ALLOY) check-layering
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' ! -path '*/tests/integration/*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec $(ALLOY_FLAGS) -c "*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect"; exit 1; fi; \
	echo "OK: all unit-tier commands matched their expect"

## check-integration: the GATE tier (DT-017) — only tests/integration/ roots (real implementations
## composed across layers; big, expensive — run at gates, always before push via check-alloy)
check-integration: $(ALLOY)
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy -path '*/tests/integration/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec $(ALLOY_FLAGS) -c "*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect"; exit 1; fi; \
	echo "OK: all integration-tier commands matched their expect"

## test-unit: run only unit_* commands across all test roots
test-unit: $(ALLOY)
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' ! -path '*/tests/integration/*' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) exec $(ALLOY_FLAGS) -c "unit_*" -o $(OUT) -f "$$f" > out/.run.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "FAIL: a command did not match its expect"; exit 1; fi; \
	echo "OK: all unit_* commands matched their expect"

## test-sys: run the whole-system suite (sys_* in alloy/tests/system.als)
test-sys: $(ALLOY)
	@mkdir -p $(OUT); \
	java -jar $(ALLOY) exec $(ALLOY_FLAGS) -c "sys_*" -o $(OUT) -f alloy/tests/system.als > out/.run.log 2>&1; rc=$$?; \
	grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	if [ $$rc -ne 0 ]; then echo "FAIL: a command did not match its expect"; exit 1; fi

## soak: the SCOPE-DESCENT tier (DT-022 TQ-5 ruling; scaling-outlook to-do #5, built 2026-08-08)
## — the gate's key laws re-checked at GENEROUS scopes (alloy/soak/tests/*.als; excluded from
## every regular tier by the '! -path alloy/soak/*' filters above). Hunts counterexamples the
## dev-loop's census-tuned pins cannot represent (the starved-scope folklore). HOURS-long;
## run scheduled/overnight, NEVER on the push path — the push gate stays check-alloy.
## Sequential by design: one JVM at a time gets the machine's full memory.
soak: $(ALLOY)
	@mkdir -p $(OUT); fail=0; \
	for f in $$(find alloy/soak \( -path '*/lemmas/*' -o -path '*/sliced/*' -o -path '*/tests/*' \) -name '*.als' | sort); do \
	  echo "== $$f =="; \
	  java -jar $(ALLOY) -D info exec $(ALLOY_FLAGS) -c "*" -o $(OUT) -f "$$f" > out/.soak.log 2>&1 || fail=1; \
	  grep -iE 'SAT|UNSAT|error|against expectation' out/.soak.log | grep -ivE 'symmetr|kodkod|cnf|translat|solving' || true; \
	done; \
	if [ $$fail -ne 0 ]; then echo "SOAK FAIL: a command did not match its expect (a law may have a counterexample past the gate scopes)"; exit 1; fi; \
	echo "OK: soak tier matched every expect"

## soak-plan / soak-chunk / soak-status / soak-harvest: the CHUNKED soak runner (DT-024 §6,
## hardened per PDEV-1610/DT-025) — night-window execution at command granularity. soak-chunk
## mints a batch dir soak/<YYYYMMDD-HHMM>/ (REJECTED on name conflict — never overwrite a batch
## ledger), stamps the model SHA into batch.meta, plans, then dispatches heaviest-first while
## the window affords each command (2x margin; unknown estimate needs >4h remaining). LENIENT=1
## (the default) never interrupts an over-runner at WINDOW end — those are SURFACED for the
## human kill/extend decision. ORTHOGONALLY, the budget-cap watchdog kills any command past
## CAP_NUM x estimate (UNKNOWN_CAP when unmeasured; 6h default) and records it OVER-BUDGET —
## a frontier bracket point, not a loss. Chunk REFUSES to start beside a foreign Alloy solver
## (FORCE=1 overrides). Done-SAT -o dumps auto-register into corpus/manifest.tsv at completion;
## soak-harvest [BATCH=…] back-fills a pre-hook batch. RESUME=soak/<tag> continues a prior batch.
## Wrapped in caffeinate when available (independent power assertion; coexists with Amphetamine).
## WINDOW accepts 16h / 45m / plain seconds. Estimates: alloy/soak/estimates.tsv, keyed by
## scope-hash — a model change under a command invalidates its measurement (row goes unknown).
soak-chunk: $(ALLOY)
	@w='$(WINDOW)'; [ -n "$$w" ] || { echo "usage: make soak-chunk WINDOW=16h [PAR=2] [LENIENT=1] [RESUME=soak/<tag>]"; exit 2; }; \
	case "$$w" in *h) s=$$(( $${w%h} * 3600 ));; *m) s=$$(( $${w%m} * 60 ));; *) s=$$w;; esac; \
	if [ -n "$(RESUME)" ]; then batch='$(RESUME)'; [ -f "$$batch/plan.tsv" ] || { echo "RESUME: no plan.tsv in $$batch"; exit 2; }; \
	else batch=soak/$$(date +%Y%m%d-%H%M); [ ! -e "$$batch" ] || { echo "REJECT: $$batch already exists (never overwrite a batch ledger)"; exit 2; }; \
	  tools/soak-chunk.sh plan "$$batch" || exit 2; fi; \
	caf=""; command -v caffeinate >/dev/null && caf="caffeinate -i"; \
	echo "batch=$$batch window=$${s}s par=$(or $(PAR),1) lenient=$(or $(LENIENT),1)"; \
	$$caf tools/soak-chunk.sh chunk "$$batch" "$$s" "$(or $(PAR),1)" "$(or $(LENIENT),1)"

soak-plan:
	@batch=soak/$$(date +%Y%m%d-%H%M)-plan; tools/soak-chunk.sh plan "$$batch"; cat "$$batch/plan.tsv"

soak-status:
	@b='$(BATCH)'; [ -n "$$b" ] || b=$$(ls -d soak/2* 2>/dev/null | sort | tail -1); \
	[ -n "$$b" ] || { echo "no batch under soak/"; exit 2; }; \
	tools/soak-chunk.sh status "$$b"

soak-harvest:
	@b='$(BATCH)'; [ -n "$$b" ] || b=$$(ls -d soak/2* 2>/dev/null | sort | tail -1); \
	[ -n "$$b" ] || { echo "no batch under soak/"; exit 2; }; \
	tools/soak-chunk.sh harvest "$$b"

## cnf-export: the CNF artifact cache (PDEV-1609 program) — export a command's Kodkod
## translation as gzipped DIMACS under cnf/<scope_hash>/, indexed in cnf/manifest.tsv.
## Keyed by (command, cone hash, alloy version); model_sha stamped for browsing. A cache
## key hit is a no-op (FORCE=1 re-exports). cnf/ is gitignored — a regenerable build
## product, the model's "class files"; conventions in knowledge-base/soak-corpus-and-budget-caps.md.
cnf-export: $(ALLOY)
	@r='$(ROOT)'; c='$(COMMAND)'; [ -n "$$r" ] && [ -n "$$c" ] || { echo "usage: make cnf-export ROOT=alloy/.../file.als COMMAND=soak_..."; exit 2; }; \
	tools/cnf-export.sh "$$r" "$$c"

## profiles: per gate root, print the adopted modeling profiles (transitive open walk — DT-012)
profiles:
	@for f in $$(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' | sort); do \
	  seen=""; queue="$$f"; \
	  while [ -n "$$queue" ]; do \
	    cur=$$(echo "$$queue" | head -1); queue=$$(echo "$$queue" | tail -n +2); \
	    case " $$seen " in *" $$cur "*) continue;; esac; seen="$$seen $$cur"; \
	    deps=$$(grep -E '^open [a-z]' "$$cur" 2>/dev/null | awk '{print $$2}' | sed 's|\[.*||; s|$$|.als|; s|^|alloy/|'); \
	    for d in $$deps; do [ -f "$$d" ] && queue=$$(printf '%s\n%s' "$$queue" "$$d"); done; \
	  done; \
	  profs=$$(echo "$$seen" | tr ' ' '\n' | grep 'meta/profiles/' | grep -v 'profile.als' | grep -v '/tests/' | sed 's|.*profiles/||; s|.als||' | sort -u | tr '\n' ' '); \
	  echo "$$f: $${profs:-<a la carte>}"; \
	done

## report: run every test-root command and print its LOGICAL outcome (exists/forall/forbidden, ok/mismatch)
report: $(ALLOY)
	@bash tools/alloy-report.sh

## report-examples: same, for the modeling cookbook
report-examples: $(ALLOY)
	@bash tools/alloy-report.sh --examples

# NOTE: the former `check-owl` target validated the authored owl/kanban.ttl, which has been
# removed (we no longer maintain an authored ontology). ROBOT is retained (`make tools`) for
# ad-hoc consultation of the vendored public standards under owl/imports/ — see owl/README.md.

## check: run all checks
check: check-alloy check-examples

## clean: remove generated Alloy exec output
clean:
	@rm -rf out
