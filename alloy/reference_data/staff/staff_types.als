module reference_data/staff/staff_types

// LOG-CARRIED since DT-023 cut 7c (MP: "staff MAY share the reference-data mechanisms" —
// third exchange; supersedes the QUASI-STATIC scope note): StaffMember rides the subject_log
// spine with the SIMPLE reference-data lifecycle. MINIMALITY DEVIATION from the R1 sketch
// (deliberate, DT-011 budget discipline): `name` stays IDENTITY (rename is not modeled), so
// the versioned state is STATUS-ONLY and the Update kind is omitted as vacuous — Create and
// Delete are the whole operation surface. R4 stands: runtime v1 keeps the order assignee as
// a text field (typealias marker); this module's runtime counterpart lands later
// (conformance caveats in PDEV-1478).

/*
 * STAFF — TYPES (DT-022 TQ-7(b), MP ruling 2026-08-07; DT-017 four-file architecture).
 * StaffMember represents a PERSON OR OTHER AGENT IN THE REAL WORLD (not to be confused
 * with system agents/principals — meta/principal is the occurrence-provenance identity;
 * a StaffMember is DOMAIN reference data: who can be assigned, named, held accountable
 * in business documents). Opaque identity + tenant-unique readable name; the lifecycle
 * status rides the log; richer characterization (contact, roles, systems identity
 * linkage) comes later.
 */

open meta/profiles/domain_log        // PROFILE (DT-012): log anatomy + group/order premises
open meta/kernel                     // Scoped, EntityId, resolve
open meta/subject_log/subject_log[StaffMember, StaffState] as stlog   // the SPINE
open meta/subject_log/lifecycle[StaffMember, StaffState] as lc       // the SHAPES: Create / Retire (DT-030, 2026-09-09)
open reference_data/shared/lifecycle // RRetiredRef (DT-023)

/** StaffName — a staff member's readable name (opaque; content is runtime data). */
sig StaffName {}

/** StaffMember — a person or other real-world agent known to a tenant (assignable,
    accountable); reference data, NOT a system principal. Identity = the immutable name;
    the lifecycle status rides the log. */
sig StaffMember extends Scoped { name: one StaffName }

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact StaffMemberRefs { all s: StaffMember | no s.dataRefs }

// Tight by default: no orphan names — StaffName is staff-local (single consumer).
fact NoOrphanStaffName { all n: StaffName | n in StaffMember.name }

// ── the state record ────────────────────────────────────────────────────────────────────────────
/** StaffState — one moment's versioned payload of a StaffMember: FIELDLESS (name is identity; nothing else is
    modeled yet; the lifecycle is the LOG's shape since 2026-09-09 — Live while the head is not a Retire). A value
    with no fields is one value. */
sig StaffState extends Snapshot {}
fact StaffStateExtensional { lone StaffState }

// ── the kinds — the reference-data lifecycle, Update omitted (fieldless state) ─────────────────
/** StaffOcc — the staff log's occurrence family; the PIN TYPE (DT-023 R3). A SUBSET sig equal to the whole log
    (the kinds sit under the lifecycle SHAPES, so the family cannot be their `extends` parent). */
sig StaffOcc in stlog/SubjectOcc {}
fact StaffOccIsTheLog { StaffOcc = stlog/SubjectOcc }
/** Create — births the StaffMember (live: the head is not a retire). */
sig CreateStaffOcc extends lc/CreateOcc {} { bindings = subject }
/** Retire — ends the StaffMember's history (the tombstone; terminal). Was DeleteStaffOcc; MP's word 2026-09-09. */
sig RetireStaffOcc extends lc/RetireOcc {} { bindings = subject }

// ── the Reason taxonomy (module-sovereign; RRetiredRef is shared via lifecycle) ─────────────────
one sig RStaffExists, RStaffNotCreated, RStaffRetired extends Reason {}

// ── the read API ────────────────────────────────────────────────────────────────────────────────
/** staffStateAt — the member's versioned content as of `t` (LOCF; none before Create). */
fun staffStateAt[s: StaffMember, t: Tick]: lone StaffState { stlog/recordAt[s, t] }
/** staffVersionAt — the member's CURRENT VERSION at `t` (what a new pin must reference). */
fun staffVersionAt[s: StaffMember, t: Tick]: lone StaffOcc { stlog/lastTouch[s, t] & StaffOcc }
/** staffLiveAt — the member exists and is Live at `t` (the reference-target guard read). */
pred staffLiveAt[s: StaffMember, t: Tick] { lc/liveSubjectAt[s, t] }
/** pinsCurrentStaff — `p` is the current version of its own member at `t` (pin currency). */
pred pinsCurrentStaff[p: StaffOcc, t: Tick] { p = staffVersionAt[p.subject, t] }
/** staffPinnableAt — current at `t` AND Live (what an introducing occurrence may pin). */
pred staffPinnableAt[p: StaffOcc, t: Tick] {
  pinsCurrentStaff[p, t] and p not in lc/RetireOcc
}
