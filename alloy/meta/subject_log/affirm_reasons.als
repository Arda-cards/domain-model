module meta/subject_log/affirm_reasons

/*
 * The AFFIRM kind's own refusal atom, declared ONCE (non-parametric — the intent_log/semantics precedent: a parametric
 * module's `one sig` would be instantiated per `open`, giving one concept N atoms). Opened by meta/subject_log/affirm.
 */

open meta/action/outcome   // Reason

/** RStaleAffirmation — the source affirms a version that is not the subject's current record. */
one sig RStaleAffirmation extends Reason {}
