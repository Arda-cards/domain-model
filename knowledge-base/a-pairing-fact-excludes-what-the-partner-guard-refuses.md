# A pairing fact excludes what the partner's guard refuses — mirror the partner's arms on the act

**Symptom (MF-002 and MF-003, found by the Dafny port, ruled 2026-10-16):** two acts the domain
expects to be REFUSED with a reason were instead absent from every instance. No command failed,
because the run asking for the refusal was never written and the universe simply lacked the case.

- A transfer citing an origin that the destination pool already carries (MF-002).
- An honest delivery retry after a refused wrong-pool create (MF-003).

**Mechanism:** a composite act is two rows tied by a FACT that demands a committed partner:

- `TransferPairing`: a committed transfer has a committed paired add on `to`.
- `createRecordsAtomically`: a committed create has a committed record, and the reverse.

The first row's guard is evaluated on its own; the partner's guard is evaluated on the partner. When the first row is
admitted but the partner's guard fires, the fact cannot be met. The solver then drops the whole instance. The
attempt is EXCLUDED: no refusal, no reason, and the admission witness (`admission = Accepted iff no viol`) would have
called it admitted.

- MF-002: the paired add's own `archeDuplicate` fires on `to`, and the transfer's guard had no matching arm.
- COORDINATOR-Q527 (the same day, found independently by the Copilot review of PR #6): a transfer dated before its
  destination's newest write had no admissible pair, because the paired add carries the transfer's stamp and its own
  `RBackdatedPoolWrite` arm fires. The fix was the same: a destination arm on the transfer
  (`poolBackdatedViol[o, o.to]`), with its own witness.
- MF-003: the record's item arm read a REFUSED create, so the retry's record was refused while the fact demanded it.

**The rule.** For every pairing fact, each way the PARTNER's guard can fire must be either:

1. **mirrored** as an arm on the initiating act, so the composite is refused there, with the partner's reason
   (MF-002: the transfer's destination-side `RDuplicateOrigin` arm tests the slot the paired add's `archeDuplicate`
   tests); or
2. **impossible** for a partner of an admitted act, because the partner's range excludes it (MF-003: the record's
   arm reads COMMITTED creates only, so a refused create cannot poison the retry).

A guard arm that ranges over rows of any verdict (`some c: CreateDeliveryOcc | …`) is a smell next to a pairing fact:
refused rows are history, not state, and a pairing partner should read state.

**How to test for it.** Write the run that asks for the refusal (or for the honest retry to commit) and confirm it is
UNSAT before the fix: an UNSAT where the domain expects a SAT is the exclusion. These cases sit at scopes the unit roots
rarely reach, two pools carrying one origin or two creates under one delivery, so build them on purpose. The Dafny
follower found both because its proofs are unbounded (`dafny-domain` MAPPING.md, findings MF-002 and MF-003).
