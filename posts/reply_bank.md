# Reply bank — boundary-axiom launch

Short, non-defensive answers. Use the strongest point; do not add new claims.

---

**Q1. Isn’t this just the standard Moore-family / closure-operator correspondence?**

Yes. The correspondence and the representation theorem are standard; I say so in
the post. The contribution is the operationalization of the report family, the
v1.0 degeneration audit, the explicit negative control, and the gate. If the
standard result is the whole interest for you, the useful question is whether the
operationalization earns its keep.

**Q2. Isn’t “boundary = report” a tautology by definition?**

It would be if `R` were defined as `Fix(C)`. It is not. `c_R` is built from an
arbitrary `R`, and the identity `R = Fix(c_R)` holds exactly on Moore families.
The non-Moore witness `P(Fin 2) ∖ {∅}` is a machine-checked failure. The v1.0
`UpClosed` version *was* degenerate; that is why v1.1 uses Moore.

**Q3. Where is the attribution → closure bridge?**

Open. The current core starts from a closure operator; it does not derive one
from the attribution presheaf. There is also a type/level gap: the attribution
layer is type-valued and needs a global section; the sharpness closure is
point-level, while the Moore result is set-level.

Public statement: `/open-bridge.html`. I would rather say this plainly than let
the report-identity result be read as having closed it.

**Q4. You say “self-awareness”; isn’t that overreach?**

The sentence “the core content of self-awareness is the capacity to identify,
represent, and maintain the boundary between self and non-self” is the
programme’s **premise**, not a theorem. The formal result is conditional and
functional: it concerns a closure operator and a report family. The release does
not claim a theory of consciousness.

**Q5. Why 33? Why 45? Why 467?**

Different scopes:

- A-module (`BoundaryTheory`): 1 file, 33 theorems/lemmas, 7 definitions.
- Report-identity core (`report-core/`): 6 modules, 45 theorems/lemmas, 13
  definitions.
- Full verified corpus (`lean/`): 56 files, 467 theorems/lemmas, 90 definitions.

They are not additive. Quote the scope with the number.

**Q6. Is the gate production-safe?**

No claim. It is a finite-state reference implementation. It shows the protocol can
execute, reject, commit atomically, and deny stale actions. It does not show that
a deployed agent cannot bypass it. The acceptance/rejection rates on a real task
are unknown.

**Q7. What is actually novel here?**

Not the Moore/closure math. The release’s contribution is the combination:
report family as a commit constraint; the v1.0 degeneration audit; the explicit
non-Moore negative control; the R1–R7 reference gate; and the public separation
of the open bridge from the proved core. If that combination is not interesting
to you, the math is standard and the post should be judged on the application.

**Q8. Why not just use a log with a signature?**

A signature can make a log tamper-evident; it does not make the log a condition on
which state is legally committable. The Moore condition is about the relation
between the report family and the boundary operator, not the integrity of a
record. You can have a perfectly signed log that is disconnected from the
boundary.

**Q9. What does “report family” mean operationally?**

It is the family of state-sets the system is willing to report as closed. The
runtime report is one element of that family. A single string is a projection;
the family is the admissible self-description. In the gate, `report ∈ R` is a
check.

**Q10. Is Moore too strong for real systems?**

Possibly. That is an open empirical/modeling question. If a natural report family
is not Moore, the identity does not apply; the gate’s R2 sends it to REVIEW. The
three-state toy example shows a per-state threshold family failing Moore. The
right response is to characterize which systems have Moore families, not to drop
the condition and keep the theorem.

**Q11. What about `w` / the level parameter?**

`V(κ)` fixes `κ*`, not `w`. `c(κ, μ, w)` depends on `w/κ`; joint scaling is a
parameterization redundancy, not a free gauge direction for `w` at fixed `κ*`.
The current gate must take `w` as an input or adopt a separate selection
principle. A unique level is not proved.

**Q12. What about A7 and the potential?**

`V_form_forced` is a model-class theorem under A7 (maintenance cost is a continuous
additive functional). The proof kernel is `map_real_smul` (continuous additive ⇒
linear), not the free-category universal property. Whether A7 can be derived from
a stronger categorical structure is open.

**Q13. How would I falsify this?**

Three routes:

1. a non-Moore report family with a non-vacuous boundary–report identity;
2. a concrete gate bypass: a committed bundle whose boundary and report disagree
   in a way R1–R7 do not catch;
3. an empirical system whose report family is Moore but whose boundary/report
   still come apart in the sense the architecture forbids.

**Q14. Is this peer-reviewed?**

No. It is a research release; papers are preprints in preparation. The Lean
artifacts are machine-checked in their stated scopes; the philosophical and
modeling claims are not.

**Q15. Why should an alignment researcher care?**

Because most agent architectures treat self-monitoring as an add-on: a monitor
observes and logs, while the action path remains separate. The Moore condition is
a precise way to ask whether the report is structurally part of the boundary
rather than an observer’s annotation. Even if the condition is too strong for
current systems, the failure mode is informative.

**Q16. What is the single most useful critique you could get?**

“Your report family is not Moore, and here is a natural system where the identity
still does something non-trivial.” That would force a weaker condition or a
different construction. The second most useful is a gate bypass.
