module shared/backdating

/*
 * BACKDATING — the refusal FAMILY for a step that would make a log's history invalid in domain time
 * (COORDINATOR-Q527, MP's ruling 2026-10-15: "We will likely find more cases like this where a
 * 'back-dated' update would create an invalid history for an entity instance or a related set of
 * instances. This is probably worth a dedicated Refusal family of which this would be the first
 * expression." Names carry the family prefix, MP's pick.)
 *
 * The condition is stated in CAUSALITY (MP's guidance, same ruling): a log whose kinds opt in to the
 * domain-time stamp (`meta/occurrence/timed`: `Timed`) promises that its stamps are monotone along
 * its OWN committed causal order; a step is REFUSED, never accepted, when admitting it would break
 * that promise on the trace it reads — the trace law is a THEOREM of the refusing guards, never an
 * assumed premise (`clocksAligned` stays the opt-in premise it is). Each adopting module declares
 * its own members beside its other reasons (the `RRetiredRef` sharing precedent,
 * reference_data/shared/lifecycle.als): `RBackdatedPoolWrite` (inventory_pool: a write dated before
 * the pool's newest write) and `RBackdatedHolding` (demand: a COMPLETE dated before its holding
 * pool's newest write). A caller matches the family or one member.
 */

open meta/action/outcome     // Reason
open meta/occurrence/timed   // Timed, atOrBefore — the stamp the members compare

/** RBackdated — the family: the step's domain-time stamp is out of causal order with the history it
    reads or closes. Abstract — the members are the adopting modules'. */
abstract sig RBackdated extends Reason {}
