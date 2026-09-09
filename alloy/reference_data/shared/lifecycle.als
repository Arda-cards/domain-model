module reference_data/shared/lifecycle

/*
 * Reference-data LIFECYCLE vocabulary (DT-023 R1, MP ruling 2026-08-10): the SIMPLE
 * log-carried lifecycle every proper reference-data module adopts —
 *
 *   [*] -> Live: Create ; Live -> Live: Update ; Live -> Retired: Retire ; Retired -> [*]
 *
 * SINCE 2026-09-09 (DT-030, MP's row-3 word: reference data converts to the generic retire) the two statuses are
 * NOT a record field: Live / Retired is the SHAPE of the log — a subject is live while its head is not a retire
 * kind (`meta/subject_log/lifecycle`: `liveSubjectAt`, `RetireOcc`, terminality). `RdStatus` / `RD_LIVE` /
 * `RD_RETIRED` are gone with the field; each module's `Retire…Occ extends lc/RetireOcc` is the terminal act.
 * (Reinstate stays a deliberately free future seam — a new kind on the log.) KINDS stay per-module (flat
 * namespace) — this file carries only the shared consumer-side refusal reason.
 *
 * SHARING SCOPE (DT-023 R2): item, business_affiliate, and staff MAY share this module.
 * `resources/processing_network` deliberately does NOT open it — Station/Loop are not
 * proper reference data and will acquire richer lifecycles; they repeat the pattern with
 * their own atoms rather than tie structurally to this vocabulary (repetition is the
 * accepted price of independence — MP, 2026-08-10).
 */

open meta/action/outcome   // Reason

/** RRetiredRef — the consumer-side refusal (DT-023 D2): an occurrence introducing a
    reference to a reference-data target whose current version at the occurrence's tick is
    Retired. One shared atom, same semantics in every consumer module (the RForeignRef
    naming precedent, hoisted here because the SAME rule guards every reference-data
    target). */
one sig RRetiredRef extends Reason {}
