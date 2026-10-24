# The open bridge: attribution → closure

This note records the one structural gap that a reader should not mistake for a
result of the report-identity core.

## The gap

The programme begins with an attribution presheaf

\[
A:\mathbf{Caus}^{\mathrm{op}}\to\Delta^2.
\]

The core begins with a closure operator `C` on a state space `Ω`. Nothing in the
Lean development constructs `C` from `A`. The attribution module and the closure
module are separate; the bridge is not a theorem.

There is also a level mismatch:

- `A` is implemented as a **type-valued** presheaf: at each state, `A(X)` is the
  type `Simplex`, not an actual distribution.
- An actual attribution field therefore requires a **global section**
  `s : ∀ X, A(X)` compatible with the path maps. No such section is defined in the
  current development.
- The sharpness closure `c(κ, μ, w)` is a **point-level** closure `Ω → Ω`; the
  Moore representation theorem produces a **set-level** closure
  `P(Ω) → P(Ω)`. These are different types.

## What a bridge would need

A defensible route has four explicit inputs:

1. a global attribution section `s`;
2. a scalar readout `bOf(s X)` (for the boundary tails, the logistic confidence
   coordinate);
3. a path-monotonicity condition: `bOf(s X) ≤ bOf(s Y)` for every path `X → Y`,
   so the threshold fiber is stable under predecessors;
4. an alignment identity: on the logistic instance, `bOf(s X) = b(κ, μ, X)`, so
   the threshold fiber is exactly the decided set of the sharpness closure.

With these, the threshold family is a Moore chain and the closure can be
constructed. Without them, one can still build **some** Moore family from `A`,
but not the sharpness closure. Moore-ness is the easy part; the content is the
section, the path compatibility, and the alignment.

## What is not claimed

- that every attribution presheaf induces a closure;
- that `moore_iff_exists_closure` identifies the sharpness closure;
- that the point-level and set-level closures are the same object;
- that the bridge has been machine-checked.

The report-identity core is independent of this gap: it starts from a closure
operator and proves the Moore/report results conditionally. The bridge is the
next theoretical target.
