# LessWrong / Alignment Forum draft

**Working title:** The boundary is the report: a conditional identity, and the
counterexample that keeps it honest

---

Most discussions of self-boundary treat the boundary as a set of states, a
Markov blanket, or a label. The engineering version then adds a log: compute the
boundary, write what happened, act. The log is evidence for an observer. It is
not a condition on the system.

This post is about a narrower move. What if the report family is not an output
but the thing that determines which states are legally committable?

I have a small machine-checked core for one version of that move. It is
conditional, and the condition is the interesting part.

## The formal object

Let `Ω` be a state space and `R ⊆ P(Ω)` a family of state-sets the system will
report as closed. Define

`c_R(S) = ⋂ { T : S ⊆ T and T ∈ R }`.

A family is **Moore** when it is closed under arbitrary intersections. On Moore
families:

- `c_R = c_R'` iff `R = R'`;
- `R = Fix(c_I)` iff `c_R = c_I`;
- every Moore family is the fixed-point family of some closure operator.

The first is co-generation: boundary and report are two presentations of one
object. The second is stronger: a joint fixed point, not a mutual function. The
third is a representation theorem.

The condition cannot be dropped. The report family
`R = P(Fin 2) ∖ {∅}` is not Moore, and it is not the fixed-point family of its
own closure. This is not a bug in the definition; it is the precise failure mode
of "report = boundary."

The Lean core is six modules, 45 theorems/lemmas, 13 definitions, no `sorry`, no
custom axioms. The load-bearing results depend only on the standard axioms.

## Why this is not the whole programme

It would be easy to overread the result. The core does **not** say:

- that every autonomous system has a Moore report family;
- that an attribution presheaf automatically induces the closure;
- that the level parameter `w` is uniquely determined by the potential;
- that a production agent cannot bypass the gate;
- that this is a theory of consciousness.

The attribution → closure bridge is open. In the current Lean development, the
attribution layer is a type-valued presheaf; an actual attribution field would
need a global section, and the point-level sharpness closure and the set-level
Moore closure live at different types. A bridge would need a section, a value
predicate, a path-compatibility condition, and an alignment identity. That is
the next theoretical target, not a theorem in this release.

The level problem is similarly open: the potential fixes `κ*`, not `w`. A gate
must either take `w` as an input or adopt a separate selection principle.

## The engineering version

The physical metaphor is a joint commit. A candidate bundle carries the closure
operator, the report family, the runtime report, evidence, and a version. The
gate checks R1–R7: closure, Moore, `c_R = C`, report membership, version/evidence
agreement, candidate uniqueness, and parent hash. If all pass, the bundle is
committed atomically. The action gate accepts only a committed bundle.

This is a finite-state reference implementation, not a deployed system. It shows
the protocol can execute and reject. It does not show that a real agent cannot
bypass it.

## What would change my mind

1. A non-Moore report family that nevertheless supports a non-vacuous
   boundary–report identity. The current counterexample is one witness; a
   general construction would be more interesting.
2. A concrete gate bypass: a committed bundle whose boundary and report disagree
   in a way R1–R7 do not catch.
3. A derivation of the attribution bridge, or a proof that no such derivation
   exists under the programme's assumptions.

The first two are adversarial; the third is theoretical. I would rather be
corrected on any of them than defended by a slogan.

## Artifacts

- Core repository: `https://github.com/limisys/boundary-axiom`
- Full 56-file / 467-theorem corpus: `https://github.com/limisys/boundary-axiom`
- Static site: `https://limisys.github.io/boundary-axiom/`

The site has a technical note and an evidence ledger. The README states the
scope before the results.

---

**Posting notes:**

- This is a discussion post, not a paper announcement. Invite the counterexample
  first.
- Do not claim peer review or production validation.
- If commenters ask "where is the attribution bridge?", point to the open-bridge
  note; do not improvise a stronger claim.
