module meta/activation/activation

/*
 * THE ACTIVATION — the act every entity row cites. Reflects dafny-domain src/meta/activation.dfy (the reference model
 * since MP's ruling of 2026-11-04; DT-015 D1 to D3, 2026-11-05; TN-002 §3 item 1, MP's option A, Journal 193243; QA708,
 * MP 2026-11-05: the Alloy tree takes the activation shape verbatim, the activation ATOM standing for the runtime's
 * opaque activationId).
 *
 * One row of a service's ACTIVATION LOG is one call into the service, minted at the public boundary before any effect;
 * its verdict is the call's outcome. An ORIGIN is an activation that cites itself: the arrival of a cause from outside
 * (a person's act, a job, an inbound message). Every other activation cites the CALLER's activation. An ENTITY row's
 * `arche` IS the activation that wrote it (D1): entity rows are the tree's leaves — never cited, never self-citing.
 * The per-row origin law (`ArcheUnique`, DT-029 Q8) left the spine with this module (D3): one cause may have several
 * sibling effects on one subject (MP, Journal 192741).
 *
 * WHAT IS ALLOY-SHAPED HERE, and why (the mapping, for DAFNY's review):
 *  - The activation's identity is the ATOM (QA708 (a)): Dafny's `Act(id, op)` and `IdOf` have no counterpart — `=` on
 *    atoms is identity, so `IdsUnique` is free and `TickOf` is `a.tick`.
 *  - NOT parametric on the service (the plan of DT-015 said `activation[Service]`): a root holding several services
 *    (the saga and system roots) would get one `Activation` sig PER instantiation, and the two citation facts below would
 *    then demand that every row cite an atom of EVERY instance — unsatisfiable. One module, one `Activation` family,
 *    `abstract sig Service` extended by one atom per service in its implementation module.
 *  - `Call` carries no subject, kind or actor: what a call names is read from the rows that cite it (the Alloy row IS
 *    its own subject and kind), and the actor is the opt-in `meta/action/attributed` seat. A service whose operation
 *    writes two logs needs no `Op` of its own: the rows of both logs cite the one `Call`.
 *  - `EffectsFollow` and `CallersPrecede` are the kernel's `ArcheOriginPrecedes`; `TicksDisjoint` is `OneOccurrencePerTick`;
 *    the cross-service skeleton World and `NoProperCycle` are the one Occurrence universe of a root and the kernel's
 *    `unit_occ_archeNoProperCycle`. They are re-checked, not re-stated, in tests/activation.als.
 *  - A refused activation's reasons are NOT tied to its effects' (the Dafny law ties the verdict only, R4): the solver
 *    may mint any Reason for a refused Call.
 *
 * ADOPTION (DT-015 R2, R6): an implementation module opens this module, declares `one sig XService extends Service {}`
 * and states, beside its chaining fact, `fact XActivated { activated[XService, xlog/SubjectOcc] }` — one per log it
 * owns. The two citation facts are MODULE facts: every root that opens this module (directly or through an adopter)
 * holds them for every Occurrence, so every witness mints the `Call` its rows cite.
 *
 * NOT here, postponed with no partial (TN-003 row 1; TN-002 §1): the idempotency key, the registry, the lookup before
 * execute, the duplicate reason. This module is the seat they return to.
 */

open meta/action/action   // Action (admission), committed, refusedAtAdmission; transitively Occurrence (tick, arche), Tick order

/** Service — the subject of an activation log: one atom per service, declared by its implementation module. */
abstract sig Service {}

/** Activation — one call into a service: an Action on the service, citing its caller's activation or itself. Its
    verdict (`admission`) is the call's outcome, defined by its effects (`effectsAgree`), not by a guard of its own. */
abstract sig Activation extends Action { service: one Service }

/** Call — the default activation kind (DT-015 R3): one public operation on one service. */
sig Call extends Activation {} { bindings = service }

// ── D1: only activations are cited, only activations self-cite ───────────────────────────────────
/** OnlyActivationsAreCited — every occurrence cites an activation: an entity row cites the act that wrote it, an
    activation cites its caller's act or itself. Entity rows are the tree's leaves. */
fact OnlyActivationsAreCited { all o: Occurrence | o.arche in Activation }
/** OnlyActivationsSelfCite — an entity row never self-cites: it has no identity of its own in the tree. */
fact OnlyActivationsSelfCite { all o: Occurrence - Activation | o.arche != o }

/** origin — an activation citing itself: the arrival of a cause from outside the system. */
pred origin[a: Activation] { a.arche = a }
/** origins — the origins of a world (the kernel's `selfInitiated`, now exactly the self-citing activations). */
fun origins: set Activation { { a: Activation | origin[a] } }

/** effectsOf — the rows an activation wrote, among `rows`. */
fun effectsOf[a: Activation, rows: set Occurrence]: set Occurrence { { o: rows | o.arche = a } }

// ── the per-service laws (Dafny `Activated(alog, elog)`, adopted per log) ────────────────────────
/** effectsCited — every row of the log cites an activation OF THIS SERVICE: no effect without its act, and the act is the
    service's own (Dafny `EffectsCited` over the service's activation log). */
pred effectsCited[s: Service, rows: set Occurrence] { all o: rows | o.arche.service = s }
/** effectsAgree — an effect's verdict is its activation's: a committed activation's effects are all committed, a refused
    one's all refused. The act is atomic; a refused effect is still a row, as the runtime records it (Dafny `EffectsAgree`). */
pred effectsAgree[rows: set Action] { all o: rows | committed[o] iff committed[o.arche] }
/** activated — the per-service law an implementation module adopts for each log it owns, beside its chaining fact: the
    log's rows each cite an activation of the service and agree with its verdict. Following it (`ArcheOriginPrecedes`) and
    sharing no tick with it (`OneOccurrencePerTick`) are the kernel's. */
pred activated[s: Service, rows: set Action] { effectsCited[s, rows] and effectsAgree[rows] }
