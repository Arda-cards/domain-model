#!/usr/bin/env bash
# soak-chunk.sh — the DT-024 §6 chunked soak runner: command-granular queue + per-batch
# ledger + resume. SAT solving is not checkpointable, so the chunk unit is the COMMAND
# and the scheduler's job is to never dispatch one it cannot afford to finish.
#
# Subcommands (driven by the Makefile targets soak-plan / soak-chunk / soak-status):
#   plan    <batch-dir>                      enumerate (root, command) pairs into plan.tsv
#   chunk   <batch-dir> <window-s> <par> <lenient>   dispatch loop (the night window)
#   status  <batch-dir>                      fold artifacts into ledger.tsv + a summary
#   harvest <batch-dir>                      register the batch's SAT dumps into corpus/
#   harvest-one <batch-dir> <command>        one command's dumps (the completion hook)
#
# Batch dir layout (soak/<YYYYMMDD-HHMM>/ at the repo root, gitignored):
#   plan.tsv            tier  root  command  scope_hash  estimate_s   (dispatch order)
#                       `command` is what the tool's -c takes: the command's LABEL when it has one
#                       (`e7_step_w: check e7_step for ...` is the command e7_step_w), else its name.
#   batch.meta          created epoch, model_sha (+dirty flag) — the corpus provenance key
#   dispatch.log        the dispatcher's decisions (dispatched / deferred / window end)
#   cmd/<key>.log       solver output          cmd/<key>.rc     exit code
#   cmd/<key>.meta      start/end epochs, root, command      cmd/<key>.d/   harvested instances (-o)
#   cmd/<key>.overbudget    cap + elapsed when the watchdog killed the command
#                       <key> = the root's path under alloy/soak with `/` as `_`, a dot, the command
#                       (sliced_cycle_pool_inductive.e7_base): two roots may state commands of one
#                       name (every rung has e7_base), and each is its own command.
#                       A batch made before the key keeps its artifacts under the bare command name; they
#                       are read for the root their meta records (art_of), so it can be resumed.
#   ledger.tsv          materialized by `status` from plan + artifacts
#
# Estimates: alloy/soak/estimates.tsv (committed) — command<TAB>scope_hash<TAB>seconds.
# An estimate counts ONLY if its scope_hash still matches (a model change under the
# command invalidates the measurement); otherwise the command is UNKNOWN and dispatches
# only while remaining window > UNKNOWN_FLOOR. Harvest new measurements from ledger.tsv.
#
# Lenient mode (MP, 2026-08-11): runs are never interrupted on going over estimate or
# WINDOW — over-runners are SURFACED at window end for a human kill/extend decision.
# ORTHOGONAL to that, the budget-cap watchdog (PDEV-1610 / DT-025 R2): a command past
# CAP_NUM x its estimate (UNKNOWN_CAP when unmeasured) is killed and recorded
# OVER-BUDGET — a deliberate "too hard at this scope" bracket data point for the
# frontier search, not a lost run. CAP_NUM=0 (or UNKNOWN_CAP=0) disables the watchdog.
#
# Quiet window (PDEV-1610): chunk REFUSES to start while a foreign Alloy solver runs on
# this host (co-running poisons both runs' wall-clocks). FORCE=1 overrides.
#
# Corpus (DT-025 R3, bulk tier): every done-SAT command's -o dumps are registered into
# corpus/manifest.tsv at completion (dumps stay in place in the batch dir; the manifest
# is the index, keyed by model_sha + scope_hash). corpus/ is gitignored — the curated
# seed corpus is a separate, committed artifact (PDEV-1613).
set -u

ALLOY_JAR=${ALLOY_JAR:-tools/alloy.jar}
ALLOY_FLAGS=${ALLOY_FLAGS:--s glucose}
MARGIN_NUM=${MARGIN_NUM:-2}          # dispatch iff estimate * MARGIN <= remaining
UNKNOWN_FLOOR=${UNKNOWN_FLOOR:-14400} # unknown estimate: dispatch only if remaining > 4h
POLL=${POLL:-60}                      # dispatcher poll interval, seconds
CAP_NUM=${CAP_NUM:-3}                 # watchdog: kill at estimate * CAP_NUM (0 disables)
UNKNOWN_CAP=${UNKNOWN_CAP:-21600}     # watchdog cap for unknown-estimate commands: 6h (0 disables)
CORPUS=${CORPUS:-corpus}              # bulk-corpus root (gitignored)
FORCE=${FORCE:-0}                     # 1 = override the quiet-window refusal

die() { echo "soak-chunk: $*" >&2; exit 2; }

# ── the cone hash: root file + its transitive `open` closure (matches `make profiles`) ──
cone_hash() { # $1 = root .als path
  local seen="" queue="$1" cur deps d
  while [ -n "$queue" ]; do
    cur=$(printf '%s\n' "$queue" | head -1); queue=$(printf '%s\n' "$queue" | tail -n +2)
    case " $seen " in *" $cur "*) continue ;; esac
    seen="$seen $cur"
    deps=$(grep -E '^open [a-z]' "$cur" 2>/dev/null | awk '{print $2}' \
           | sed 's|\[.*||; s|$|.als|; s|^|alloy/|')
    for d in $deps; do [ -f "$d" ] && queue=$(printf '%s\n%s' "$queue" "$d"); done
  done
  # shellcheck disable=SC2086
  cat $seen | shasum -a 256 | awk '{print substr($1,1,16)}'
}

soak_roots() { # tier order: lemmas, sliced, then the transitional tests/
  { find alloy/soak -path '*/lemmas/*' -name '*.als' | sort
    find alloy/soak -path '*/sliced/*' -name '*.als' | sort
    find alloy/soak -path '*/tests/*'  -name '*.als' | sort; } 2>/dev/null
}

tier_of() { case "$1" in */lemmas/*) echo 0;; */sliced/*) echo 1;; *) echo 2;; esac; }

# ── the commands a root states, one per line: the label when the command has one, else its name ──
commands_of() { # $1 = root .als path
  sed -nE 's/^[[:space:]]*(([A-Za-z_][A-Za-z_0-9]*)[[:space:]]*:[[:space:]]*)?(run|check)[[:space:]]+([A-Za-z_][A-Za-z_0-9]*).*/\2 \4/p' "$1" \
    | awk '{print $1}'
}

# ── the artifact key of a (root, command) pair: unique across roots that share a command name ──
key_of() { # $1 = root .als path  $2 = command
  printf '%s.%s\n' "$(printf '%s' "$1" | sed -E 's|^alloy/soak/||; s|\.als$||; s|/|_|g')" "$2"
}
# ── where a (root, command) pair's artifacts are in a GIVEN batch: under its key, or, in a batch made before the key
# existed, under the bare command name when that name's meta records this root (a same-named command of another root
# then reads as pending, which it was: the old runner skipped it) ──
art_of() { # $1 = batch dir  $2 = root .als path  $3 = command
  local k; k=$(key_of "$2" "$3")
  if [ ! -e "$1/cmd/$k.meta" ] && [ -f "$1/cmd/$3.meta" ] \
     && [ "$(awk -F'\t' '$1=="root"{print $2}' "$1/cmd/$3.meta" 2>/dev/null)" = "$2" ]; then
    printf '%s\n' "$3"
  else
    printf '%s\n' "$k"
  fi
}
# the same key, computed by awk from plan.tsv's columns 2 (root) and 3 (command)
AWK_KEY='function key(r, c) { sub(/^alloy\/soak\//, "", r); sub(/\.als$/, "", r); gsub(/\//, "_", r); return r "." c }'

# ── foreign solvers (quiet window): Alloy JVMs on this host NOT belonging to $1 ──────
foreign_solvers() { # $1 = batch dir (our own jobs carry "-o <batch>/" in their args)
  ps -axo pid,command | grep -F 'alloy.jar' | grep -v grep | grep -vF "$1/" || true
}

# ── plan ─────────────────────────────────────────────────────────────────────────────
cmd_plan() {
  local batch="$1" est=alloy/soak/estimates.tsv root h tier c e
  mkdir -p "$batch/cmd"
  { printf 'created\t%s\n' "$(date +%s)"
    printf 'model_sha\t%s\n' "$(git rev-parse HEAD 2>/dev/null || echo unknown)"
    printf 'dirty\t%s\n' "$([ -n "$(git status --porcelain 2>/dev/null)" ] && echo 1 || echo 0)"
  } > "$batch/batch.meta"
  : > "$batch/plan.unsorted"
  for root in $(soak_roots); do
    h=$(cone_hash "$root"); tier=$(tier_of "$root")
    for c in $(commands_of "$root"); do
      e=-1
      [ -f "$est" ] && e=$(awk -F'\t' -v c="$c" -v h="$h" '$1==c && $2==h {print $3; exit}' "$est")
      [ -n "$e" ] || e=-1
      printf '%s\t%s\t%s\t%s\t%s\n' "$tier" "$root" "$c" "$h" "$e" >> "$batch/plan.unsorted"
    done
  done
  # order: tier asc, then estimate DESC (heaviest first; unknown -1 sorts last), then name
  sort -t"$(printf '\t')" -k1,1n -k5,5nr -k3,3 "$batch/plan.unsorted" > "$batch/plan.tsv"
  rm -f "$batch/plan.unsorted"
  echo "plan: $(wc -l < "$batch/plan.tsv" | tr -d ' ') commands -> $batch/plan.tsv"
}

# ── chunk (the dispatcher) ───────────────────────────────────────────────────────────
launch_one() { # $1 batch  $2 root  $3 command  $4 scope_hash
  local batch="$1" root="$2" c="$3" h="$4" k
  k=$(key_of "$root" "$c")
  mkdir -p "$batch/cmd/$k.d"
  printf 'start\t%s\nscope_hash\t%s\nroot\t%s\ncommand\t%s\n' "$(date +%s)" "$h" "$root" "$c" > "$batch/cmd/$k.meta"
  nohup sh -c "java -jar '$ALLOY_JAR' -D info exec $ALLOY_FLAGS -c '$c' -o '$batch/cmd/$k.d' -f '$root' \
                 > '$batch/cmd/$k.log' 2>&1; \
               echo \$? > '$batch/cmd/$k.rc'; \
               printf 'end\t%s\n' \"\$(date +%s)\" >> '$batch/cmd/$k.meta'; \
               tools/soak-chunk.sh harvest-one '$batch' '$k' >> '$batch/dispatch.log' 2>&1 || true" \
       >/dev/null 2>&1 &
  echo "$!" > "$batch/cmd/$k.pid"
  echo "$(date '+%H:%M:%S') DISPATCH $c (root $root, pid $(cat "$batch/cmd/$k.pid"))" | tee -a "$batch/dispatch.log"
}

running_count() { # jobs with a pid file, no rc yet, process alive
  local batch="$1" n=0 p
  for p in "$batch"/cmd/*.pid; do
    [ -f "$p" ] || continue
    local c; c=$(basename "$p" .pid)
    [ -f "$batch/cmd/$c.rc" ] && continue
    kill -0 "$(cat "$p")" 2>/dev/null && n=$((n+1))
  done
  echo "$n"
}

cmd_chunk() {
  local batch="$1" window="$2" par="$3" lenient="$4"
  [ -f "$batch/plan.tsv" ] || die "no plan.tsv in $batch (run plan first)"
  local foreign; foreign=$(foreign_solvers "$batch")
  if [ -n "$foreign" ] && [ "$FORCE" != "1" ]; then
    echo "QUIET-WINDOW REFUSAL: another Alloy solver is running on this host — co-running poisons both wall-clocks (and the estimates harvested from them). FORCE=1 overrides." >&2
    echo "$foreign" >&2
    exit 2
  fi
  local start end now remaining
  start=$(date +%s); end=$((start + window))
  echo "$(date '+%H:%M:%S') CHUNK start window=${window}s par=$par lenient=$lenient cap=${CAP_NUM}x/unknown=${UNKNOWN_CAP}s" | tee -a "$batch/dispatch.log"
  while :; do
    now=$(date +%s); remaining=$((end - now))
    # ── budget-cap watchdog (PDEV-1610 / DT-025 R2): a kill here is a bracket data ──
    # point ("too hard at this scope"), never a lost run — the ledger keeps it.
    local wp wc wpid ws0 wel we wcap
    for wp in "$batch"/cmd/*.pid; do
      [ -f "$wp" ] || continue
      wc=$(basename "$wp" .pid)
      [ -f "$batch/cmd/$wc.rc" ] && continue
      [ -f "$batch/cmd/$wc.overbudget" ] && continue
      wpid=$(cat "$wp"); kill -0 "$wpid" 2>/dev/null || continue
      ws0=$(awk -F'\t' '$1=="start"{print $2}' "$batch/cmd/$wc.meta" 2>/dev/null); [ -n "$ws0" ] || continue
      wel=$((now - ws0))
      we=$(awk -F'\t' -v k="$wc" "$AWK_KEY"' key($2, $3)==k || $3==k {print $5; exit}' "$batch/plan.tsv"); we=${we:--1}
      if [ "$we" -ge 0 ]; then wcap=$((we * CAP_NUM)); else wcap=$UNKNOWN_CAP; fi
      [ "$wcap" -gt 0 ] || continue
      if [ "$wel" -gt "$wcap" ]; then
        printf 'cap_s\t%s\nelapsed_s\t%s\n' "$wcap" "$wel" > "$batch/cmd/$wc.overbudget"
        echo "$(date '+%H:%M:%S') OVER-BUDGET kill $wc elapsed=${wel}s cap=${wcap}s — recorded as a too-hard-at-this-scope bracket point" | tee -a "$batch/dispatch.log"
        pkill -TERM -P "$wpid" 2>/dev/null; sleep 5; pkill -KILL -P "$wpid" 2>/dev/null || true
      fi
    done
    # fold: revert dead 'running' rows (killed mid-solve) to pending is implicit — a pid
    # with no rc and no live process simply becomes dispatchable again on RESUME, and its
    # second death is visible in dispatch.log for the over-window judgment.
    local active; active=$(running_count "$batch")
    if [ "$remaining" -gt 0 ] && [ "$active" -lt "$par" ]; then
      local dispatched=0
      local k
      while IFS=$(printf '\t') read -r tier root c h e; do
        k=$(art_of "$batch" "$root" "$c")
        [ -f "$batch/cmd/$k.rc" ] && continue           # done (this batch)
        [ -f "$batch/cmd/$k.pid" ] && kill -0 "$(cat "$batch/cmd/$k.pid")" 2>/dev/null && continue  # running
        if [ "$e" -ge 0 ]; then
          [ $((e * MARGIN_NUM)) -le "$remaining" ] || { echo "$(date '+%H:%M:%S') DEFER $c est=${e}s remaining=${remaining}s" >> "$batch/dispatch.log"; continue; }
        else
          [ "$remaining" -gt "$UNKNOWN_FLOOR" ] || { echo "$(date '+%H:%M:%S') DEFER $c est=unknown remaining=${remaining}s" >> "$batch/dispatch.log"; continue; }
        fi
        [ -n "$(foreign_solvers "$batch")" ] && echo "$(date '+%H:%M:%S') QUIET-WARN dispatching $c while a foreign Alloy solver runs — wall-clocks (and harvested estimates) are polluted" | tee -a "$batch/dispatch.log"
        launch_one "$batch" "$root" "$c" "$h"; dispatched=1; break
      done < "$batch/plan.tsv"
      # nothing dispatchable and nothing running and window still open -> all done or all deferred
      if [ "$dispatched" -eq 0 ] && [ "$active" -eq 0 ]; then
        local pending; pending=$(while IFS=$(printf '\t') read -r tier root c h e; do [ -f "$batch/cmd/$(art_of "$batch" "$root" "$c").rc" ] || echo "$c"; done < "$batch/plan.tsv" | wc -l | tr -d ' ')
        echo "$(date '+%H:%M:%S') CHUNK idle: 0 running, $pending pending (deferred for window)" | tee -a "$batch/dispatch.log"
        break
      fi
    fi
    if [ "$remaining" -le 0 ]; then
      if [ "$active" -eq 0 ]; then
        echo "$(date '+%H:%M:%S') CHUNK window closed, nothing running" | tee -a "$batch/dispatch.log"; break
      fi
      echo "$(date '+%H:%M:%S') WINDOW END with $active still solving (lenient=$lenient) — over-runners left for the human kill/extend decision:" | tee -a "$batch/dispatch.log"
      for p in "$batch"/cmd/*.pid; do
        local c; c=$(basename "$p" .pid)
        [ -f "$batch/cmd/$c.rc" ] && continue
        kill -0 "$(cat "$p")" 2>/dev/null && echo "  RUNNING $c (pid $(cat "$p"))" | tee -a "$batch/dispatch.log"
      done
      [ "$lenient" = "1" ] && exit 0 || exit 1
    fi
    sleep "$POLL"
  done
  cmd_status "$batch"
}

# ── harvest (corpus registration — DT-025 R3 bulk tier) ─────────────────────────────
harvest_one() { # $1 batch  $2 key — idempotent (dedupes on solution path)
  local batch="$1" k="$2" c sols s sha root h n=0
  c=$(awk -F'\t' '$1=="command"{print $2}' "$batch/cmd/$k.meta" 2>/dev/null); c=${c:-$k}   # a batch from before the key: its key is the command
  sols=$(find "$batch/cmd/$k.d" -name '*solution*' -type f 2>/dev/null | sort)
  [ -n "$sols" ] || return 0
  mkdir -p "$CORPUS"
  [ -f "$CORPUS/manifest.tsv" ] || printf 'registered\tmodel_sha\troot\tcommand\tscope_hash\tbatch\tsolution\n' > "$CORPUS/manifest.tsv"
  sha=$(awk -F'\t' '$1=="model_sha"{print $2}' "$batch/batch.meta" 2>/dev/null)
  if [ -z "$sha" ]; then
    # retro batch (predates batch.meta): resolve the tip AS OF the batch's start time,
    # which the batch dir name encodes (soak/YYYYMMDD-HHMM). scope_hash stays the exact key.
    local ts; ts=$(basename "$batch" | sed -nE 's/^([0-9]{4})([0-9]{2})([0-9]{2})-([0-9]{2})([0-9]{2}).*/\1-\2-\3 \4:\5/p')
    sha=$( [ -n "$ts" ] && git rev-list -1 --before="$ts" HEAD 2>/dev/null || true )
    sha="${sha:-unknown}+retro"
  fi
  root=$(awk -F'\t' '$1=="root"{print $2}' "$batch/cmd/$k.meta" 2>/dev/null)
  h=$(awk -F'\t' '$1=="scope_hash"{print $2}' "$batch/cmd/$k.meta" 2>/dev/null)
  for s in $sols; do
    grep -qF "	$s" "$CORPUS/manifest.tsv" 2>/dev/null && continue
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date +%s)" "$sha" "${root:-?}" "$c" "${h:-?}" "$batch" "$s" >> "$CORPUS/manifest.tsv"
    n=$((n+1))
  done
  [ "$n" -gt 0 ] && echo "HARVEST $c: $n instance(s) -> $CORPUS/manifest.tsv"
  return 0
}

cmd_harvest() { # retroactive whole-batch registration (old batches predate the hook)
  local batch="$1" d c before after
  [ -d "$batch/cmd" ] || die "no cmd/ in $batch"
  before=$( [ -f "$CORPUS/manifest.tsv" ] && awk 'NR>1{n++} END{print n+0}' "$CORPUS/manifest.tsv" || echo 0 )
  for d in "$batch"/cmd/*.d; do
    [ -d "$d" ] || continue
    c=$(basename "$d" .d)
    harvest_one "$batch" "$c"
  done
  after=$( [ -f "$CORPUS/manifest.tsv" ] && awk 'NR>1{n++} END{print n+0}' "$CORPUS/manifest.tsv" || echo 0 )
  echo "harvest: $((after - before)) new instance(s) registered from $batch ($CORPUS/manifest.tsv now $after rows)"
}

# ── status (materialize the ledger) ──────────────────────────────────────────────────
cmd_status() {
  local batch="$1"
  [ -f "$batch/plan.tsv" ] || die "no plan.tsv in $batch"
  printf 'tier\troot\tcommand\tscope_hash\testimate_s\tstatus\telapsed_s\n' > "$batch/ledger.tsv"
  local nd=0 nm=0 ne=0 nr=0 np=0 nb=0
  local k
  while IFS=$(printf '\t') read -r tier root c h e; do
    local st="pending" el=""
    k=$(art_of "$batch" "$root" "$c")
    if [ -f "$batch/cmd/$k.rc" ]; then
      local rc; rc=$(cat "$batch/cmd/$k.rc")
      local s0 s1; s0=$(awk -F'\t' '$1=="start"{print $2}' "$batch/cmd/$k.meta" 2>/dev/null)
      s1=$(awk -F'\t' '$1=="end"{print $2}' "$batch/cmd/$k.meta" 2>/dev/null)
      [ -n "$s0" ] && [ -n "$s1" ] && el=$((s1 - s0))
      if [ -f "$batch/cmd/$k.overbudget" ]; then st="OVER-BUDGET"; nb=$((nb+1))
      elif grep -q "against expectation" "$batch/cmd/$k.log" 2>/dev/null; then st="MISMATCH"; nm=$((nm+1))
      elif [ "$rc" != "0" ] || grep -qE "Syntax error|\[main\] ERROR" "$batch/cmd/$k.log" 2>/dev/null; then st="ERROR"; ne=$((ne+1))
      else st="done"; nd=$((nd+1)); fi
    elif [ -f "$batch/cmd/$k.pid" ] && kill -0 "$(cat "$batch/cmd/$k.pid")" 2>/dev/null; then
      st="running"; nr=$((nr+1))
      el=$(( $(date +%s) - $(awk -F'\t' '$1=="start"{print $2}' "$batch/cmd/$k.meta") ))
    else np=$((np+1)); fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$tier" "$root" "$c" "$h" "$e" "$st" "$el" >> "$batch/ledger.tsv"
  done < "$batch/plan.tsv"
  echo "== $batch: done=$nd mismatch=$nm error=$ne over-budget=$nb running=$nr pending=$np"
  [ "$nm" -gt 0 ] && { echo "MISMATCHES (a law may have a counterexample past the gate scopes):"; awk -F'\t' '$6=="MISMATCH"{print "  "$3"  ("$2")"}' "$batch/ledger.tsv"; }
  [ "$nb" -gt 0 ] && { echo "OVER-BUDGET (too hard at this scope — frontier bracket points, candidates for the FULL profile):"; awk -F'\t' '$6=="OVER-BUDGET"{print "  "$3"  ("$2")"}' "$batch/ledger.tsv"; }
  if [ -f "$CORPUS/manifest.tsv" ]; then
    local reg; reg=$(awk -F'\t' -v b="$batch" 'NR>1 && $6==b' "$CORPUS/manifest.tsv" | wc -l | tr -d ' ')
    echo "corpus: $reg instance(s) registered from this batch"
  fi
  column -t -s "$(printf '\t')" "$batch/ledger.tsv" | sed 's/^/  /'
}

case "${1:-}" in
  plan)        shift; cmd_plan "$@";;
  chunk)       shift; cmd_chunk "$@";;
  status)      shift; cmd_status "$@";;
  harvest)     shift; cmd_harvest "$@";;
  harvest-one) shift; harvest_one "$@";;
  conehash)    shift; cone_hash "$1";;
  *) die "usage: soak-chunk.sh plan|chunk|status|harvest|harvest-one|conehash <batch-dir|root> [args]";;
esac
