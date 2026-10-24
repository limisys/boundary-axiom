# X thread — AI Alignment

**Audience:** agent foundations, evals, safety architecture.
**Angle:** a report that cannot be separated from the boundary it reports.

---

**1/**
An agent can compute a boundary and write a log without making the boundary part
of its organisation.

The log can be stale, corrupted, or disagree with the state it claims to describe.

What if the report is a constraint on what can be committed?

**2/**
The ordinary pipeline is:

state → compute boundary → write report → act

The report is an output. The system still acts if it is wrong.

The alternative: the report family is part of the state's legality condition.

**3/**
Formal core: a report family R ⊆ P(Ω), and

c_R(S) = ⋂ { T : S ⊆ T, T ∈ R }.

If R is Moore — closed under arbitrary intersections — then R and c_R determine
each other. The report family is exactly the closure's fixed-point family.

**4/**
Two strengths:

weak: c_R = c_R' ↔ R = R'  (co-generation)
strong: R = Fix(c_I) ↔ c_R = c_I  (joint fixed point)

Both conditional on Moore. The condition is not decoration.

**5/**
Drop it and the identity fails.

R = P(Fin 2) ∖ {∅} is non-Moore, and is not the fixed-point family of its own
closure. Machine-checked counterexample.

v1.0 used UpClosed; in Lean that forces R = Set.univ, so v1.0 was a tautology.
v1.1 fixed it.

**6/**
Engineering side: a finite-state gate checks R1–R7, commits the bundle
atomically, and lets actions through only after a committed bundle.

Reference implementation, not production security. 14/14 protocol tests.

**7/**
What this does NOT claim:

— not a theory of consciousness
— not every agent has a Moore family
— not the attribution → closure bridge (open)
— not a unique level w
— not production safety

The README says this before the results.

**8/**
The useful attack is adversarial:

construct a non-Moore family with a non-vacuous identity, or find a gate bypass.

Entry: limisys.github.io/boundary-axiom
Tech: …/technical.html
Code: github.com/limisys/boundary-axiom

---

**Posting notes:** attach `site/assets/og.png`; pin tweet 1; reply to objections
with `posts/reply_bank.md` answers, not improvised stronger claims.
