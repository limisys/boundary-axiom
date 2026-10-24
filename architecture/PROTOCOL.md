# Consistency Gate — protocol note

**Status:** design + finite-state reference implementation. Not a deployed
system, not a production security proof.

---

## 1. The invariant

> The system must not commit "the boundary is settled" separately from "the
> report of that boundary is settled." It commits one object in which the
> boundary operator, the report family, the runtime report, the evidence, and
> the version are bound together.

This is stronger than "write a log after computing a boundary." It removes the
legal intermediate state in which a boundary has changed and its report has not.

## 2. Bundle

| Field | Meaning |
|---|---|
| `C` | closure operator `P(Ω) → P(Ω)` |
| `R` | report family `⊆ P(Ω)` |
| `report` | runtime report; must be an element of `R` |
| `evidence` | state/trace/certificate supporting the decision |
| `certificate` | consistency check result and its hash |
| `version` | monotone version; bound to evidence |
| `parent` | hash of the previous committed bundle |

The bundle is immutable. An update produces a new bundle; it does not mutate the
old one.

## 3. Checks

| Code | Check | Failure |
|---|---|---|
| R1 | `C` is a closure operator (extensive, monotone, idempotent) | REJECT |
| R2 | `R` is a Moore family (closed under arbitrary intersections) | REVIEW |
| R3 | `c_R = C` pointwise, where `c_R(S) = ⋂{T ⊇ S : T ∈ R}` | REJECT |
| R4 | `report ∈ R` | REJECT |
| R5 | `version`, `evidence`, and `certificate` agree | REVIEW |
| R6 | exactly one candidate | REVIEW |
| R7 | `parent` equals the current committed head | REJECT |

R2 is REVIEW, not REJECT: a non-Moore family does not make the system
"broken"; it means the system cannot claim the boundary–report identity until
the family is repaired or the claim is withdrawn. A deployment may choose a hard
reject, but it must not silently pass.

R6 belongs to candidate generation. The reference implementation exposes
`gate_candidates(candidates, universe, head)`; it returns REVIEW for zero or
multiple candidates and delegates a single candidate to `gate`.

## 4. Atomic commit

```
commit(bundle):
    verdict = gate(bundle, head)
    if verdict != ACCEPT: raise CommitRejected
    transaction:
        check parent == current head
        write bundle
        set head to new hash
    # boundary, report, evidence, version land together
```

Three invariants:

- **I1:** no committed `C` without the matching `R` in the same bundle.
- **I2:** no committed `report` without the matching `C` in the same bundle.
- **I3:** no cross-version splicing of `C`, `R`, `report`, `evidence`,
  `certificate`.

These are enforced by the single `commit(bundle)` entry point and immutable
objects, not by caller discipline.

## 5. Action gate

```
execute(action, bundle):
    deny if no committed bundle
    deny if action.required_version != bundle.version
    deny if action.target is not within bundle.C(bundle.state)
    allow otherwise
```

An LLM or planner may propose an action, but it cannot hold raw action authority.
The proposal must first pass through the bundle gate.

## 6. Reference implementation

`gate_reference.py` uses only the Python standard library. It enumerates finite
state spaces, constructs closure operators and Moore families, runs R1–R7,
exercises rejection/review paths, simulates a crash before the atomic swap, and
checks the action gate.

```bash
python3 architecture/gate_reference.py
```

The tests are a protocol check. They do not measure acceptance/rejection rates on
a real task, and they do not show that a production agent cannot bypass the gate.

## 7. Known limits

- Finite state spaces only; the implementation enumerates subsets.
- No cryptographic hash in the reference store; hashes are illustrative.
- No persistence, concurrency, or adversarial runtime.
- R6 is a calling convention, not a property of a single candidate.
- The protocol does not solve the attribution→closure bridge; it starts from a
  supplied closure `C` and report family `R`.
