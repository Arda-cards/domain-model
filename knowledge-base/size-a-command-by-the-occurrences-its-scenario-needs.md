# Size a command by the occurrences its scenario needs

**Symptom (the TN-004 projection, 2026-11-11):** of 33 new finders, 5 came back UNSAT although an instance was wanted,
and 4 ran past a 180 s cap with no verdict. Not one was a defect of the model. The five had a bound on `Occurrence` one
or two below what their scenario needs. The four had a default scope of 8 to 11, which sizes every other sig of the cone
too (up to 1.08 million variables).

**The worse half of the same mistake is silent.** A `run` that is one occurrence short turns UNSAT and is seen. A
`check` whose scenario does not fit its scope stays green: it passes without examining a single case of its law.
Measured at the Alloy cut's head (`8cc322a`), on the demand's unit root: of the twelve contract checks bounded at the
default 5 occurrences, eight have no instance of their own scenario at their scope (no committed Complete, Distribute,
Remove or CreateDelivery fits in 5), and two more never meet the case their law refuses.

## What a scenario costs, in occurrences

Count the scenario's rows, then add what the kernel and the activation law make each of them bring. In a unit root
(the module's implementation over its peers' mocks):

| What the scenario has | Occurrences |
| --- | --- |
| each row of the module's own logs | 1 |
| the committed rows of one service, all together | 1 (they may cite one activation, the `Call`) |
| each distinct set of refusal reasons among the refused rows | 1 (a refused row's activation carries the same reasons) |
| a pool that must be live | 1 for its `CreatePoolOcc`; the pool service's rows share 1 more activation |
| an item pin (a demand's, a pool's, a line's) | 1 (`itemPin` is an `ItemOcc`, and `ItemOcc` is an `Occurrence`) |
| a peer under a MOCK whose status the scenario reads at k different values | k rows of that peer (a status changes only by a row; a mock's rows need no activation of their own) |

Examples, each bracketed by runs (TN-004 projection, 2026-11-11):

- A demand born with no contribution, then a refused Release: the pin, 2 rows, the committed row's activation, the
  refusal's activation: 5. An instance at exactly 5.
- A demand created, an external contribution added, released: the pin, 3 rows, 1 activation, the pool's genesis and
  the pool service's activation: 7. No instance at 6; an instance at 8.
- The same demand with the external contribution's pool carrying another item, the attach refused: a second item pin
  and the refusal's activation, less the Release: 8. No instance at 6; an instance at 9.
- Two external attaches under one id, the second refused for that alone (so its own pool must be live and fresh): the
  pin, 3 rows, 2 activations, 2 pool geneses, the pool service's activation: 9. No instance at 7; an instance at 10.

By the same count, not bracketed by a run: a committed Complete of a demand born with an external contribution is 8
(9 with one item added to its pool), and of a demand whose one member is a card under the kanban mock, 9 (the pin, 4
rows, 1 activation, and 3 rows of the cycle: accepted, in process, settled).

`Tick` is at least `Occurrence` (one occurrence per tick). `Snapshot` is the number of distinct state values, usually a
few above the row count.

## Rules

1. **Pin the log's four dimensions and keep the default small:** `for 5 but …, K Occurrence, K+1 Tick, E EntityId,
   S Snapshot`, with K the count above plus one. A default of `for 9` to reach nine occurrences also gives nine atoms to
   every other sig in the cone.
2. **A check's scope must admit its own scenario.** Before trusting a green check, ask for the case in which its
   consequent can fail (for "every committed X satisfies P": `some o: X | committed[o]`) as a `run` at the check's own
   scope. No instance means the check is empty at that scope.
3. **When a change adds an atom to every row** (the activation did, on 2026-11-05), re-size the checks as well as the
   witnesses. Re-running until every command "matches" re-sizes only the witnesses: they are the ones that turn UNSAT.
4. **Pin out what the scenario does not use** in the largest finders (`0 CardCycle`, `0 Placement`, `0 Station`, …):
   two demands in production are 13 occurrences, and at that size every unused sig costs time.

## Measuring it

Put the probe `run`s in a root of their own next to the root they measure (same `open`s, the scope clause copied from
each check), on a branch that is never merged, and run them one command per JVM. The demand's sixteen probes took 15 to
18 s each.
