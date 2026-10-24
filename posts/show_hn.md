# Show HN draft

**Title:** Show HN: A machine-checked core for boundary–report identity (Lean 4)

**Body:**

If an agent computes a boundary and writes a log, it has not thereby made the
boundary part of its own organisation. The log can be stale, corrupted, or
disconnected from the state it claims to describe.

I have been working on one structural piece of that problem: what happens when
the report is not an output but a constraint on which states the system may
commit as valid?

The formal core is small and conditional. A report family is a family of
state-sets the system will report as closed. If that family is **Moore** — closed
under arbitrary intersections — then it determines a closure operator uniquely,
and the closure's fixed-point family is the report family itself. In Lean:

- `c_R(S) = ⋂ {T ⊇ S : T ∈ R}` is always a closure operator.
- On Moore families, `c_R = c_R' ↔ R = R'`.
- `R = Fix(c_I) ↔ c_R = c_I` is the joint fixed-point form.
- The condition cannot be dropped: `R = P(Fin 2) ∖ {∅}` is an explicit non-Moore
  counterexample, machine-checked.

The release is a six-module Lean 4 core: 45 theorems/lemmas, 13 definitions, no
`sorry`, no custom axioms. The load-bearing results depend only on
`[propext, Classical.choice, Quot.sound]`.

There is also a finite-state reference gate (R1–R7): a candidate bundle carries
the closure, the report family, the runtime report, evidence, and version; the
gate either accepts it atomically or sends it to REJECT/REVIEW; the action gate
accepts only a committed bundle. The tests are protocol checks, not a production
security proof.

What this is **not**:

- It is not a theory of consciousness.
- It does not claim every system has a Moore report family.
- It does not close the attribution → closure bridge. That bridge is open; the
  core starts from a closure operator, and the attribution layer is separate.
- It does not prove a deployed agent cannot bypass the gate.

The interesting criticism for me is not "this is too abstract." It is: construct
a non-Moore report family that nevertheless supports a non-vacuous
boundary–report identity, or find a concrete pass through the gate that commits a
boundary and a report which disagree in a way the checks do not catch. The
current counterexample is the beginning of that adversarial programme, not the
end.

Repository: `https://github.com/limisys/boundary-axiom`
Static site: `https://limisys.github.io/boundary-axiom/`

The full 56-file / 467-theorem corpus is separate:
`https://github.com/limisys/boundary-axiom`.

---

**Notes for posting (not part of the post):**

- Verify the URLs after the repository is pushed and Pages is green.
- HN may strip some formatting; the plain-text version is the body above.
- Do not add a CV or personal history. The artifact is the claim.
- The honest scope paragraph is deliberate. Removing it will produce the exact
  "you formalized a tautology" objection the v1.1 correction was designed to
  avoid.
