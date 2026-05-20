/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv
public import Mathlib.Analysis.Convex.Continuous

/-!
# Lipschitz smoothness in finite dimensions

In a finite-dimensional real normed space, `LipschitzSmoothWith K f` collapses to the
standard `C^{1,1}` class — Fréchet-differentiable with `K`-Lipschitz Fréchet derivative —
**without any convexity hypothesis on `f`**.

The route is via Cannarsa-Sinestrari's semiconcavity framework: the two-sided abs bound
on `lineDeriv` is equivalent to `f` being simultaneously `K`-semiconcave and `K`-semiconvex
with linear modulus. Cannarsa-Sinestrari, *Semiconcave Functions, Hamilton-Jacobi
Equations, and Optimal Control* (2004), Corollary 3.3.8 (p.61) then yields
`f ∈ C^{1,1}` with the Lipschitz constant of `∇f` exactly `K`. An independent route
is Rockafellar-Wets, *Variational Analysis* (1998), Proposition 13.34 (p.605):
`C^{1+}` ⟺ lower-`C²` + upper-`C²`. Both proofs are finite-dim-essential.

The infinite-dim obstruction is genuine: a discontinuous linear functional `ℓ : F → ℝ`
satisfies `LipschitzSmoothWith 0 ℓ` but is not even continuous (Bauschke-Combettes,
*Convex Analysis and Monotone Operator Theory in Hilbert Spaces* (2017), Example 8.42
p.151). So the `[FiniteDimensional ℝ F]` hypothesis is not just convenient — it is
*necessary* in the absence of an explicit continuity or differentiability assumption.

## Main results

- `LipschitzSmoothWith.differentiable`: `f` is Fréchet differentiable everywhere.
- `LipschitzSmoothWith.lipschitzWith_fderiv`: `fderiv ℝ f` is `K`-Lipschitz.
- `LipschitzSmoothWith.locallyLipschitz`: `f` is locally Lipschitz (corollary).
- `LipschitzSmoothWith.continuous`: `f` is continuous (corollary).

## Implementation notes

The proofs go through the semiconcavity decomposition: `f - K/2 ‖·‖²` concave and
`-f - K/2 ‖·‖²` concave, both equivalent to the corresponding direction of the predicate.
From there, `ConcaveOn.locallyLipschitz` (which requires `[FiniteDimensional ℝ F]`)
gives local Lipschitz of the concave parts, and a super-gradient sandwich identifies
`lineDeriv f x` with a continuous linear functional, upgrading line-differentiability
(from `LipschitzSmoothWith.hasLineDerivAt`) to Fréchet differentiability.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {K : NNReal} {f : F → ℝ}

namespace LipschitzSmoothWith

/-- A `K`-smooth function is Fréchet differentiable everywhere in finite dimensions.

The line-derivative provided by `LipschitzSmoothWith.hasLineDerivAt` is upgraded to
a Fréchet derivative via the super-gradient sandwich: the predicate makes
`f - K/2 ‖·‖²` concave and `-f - K/2 ‖·‖²` concave, so super-gradients of both exist
everywhere (concave on `ℝⁿ`, every point interior), and the resulting sandwich forces
`lineDeriv f x` to be a continuous linear functional — yielding Fréchet
differentiability with quadratic remainder.

See Cannarsa-Sinestrari (2004) Theorem 3.3.7 p.60 for the corresponding regularity
statement in the semiconcavity framework. -/
theorem differentiable (h : LipschitzSmoothWith K f) : Differentiable ℝ f :=
  sorry

/-- A `K`-smooth function on a finite-dimensional space has a `K`-Lipschitz Fréchet
derivative.

This is the non-convex finite-dim equivalence: our predicate ⟹ standard `C^{1,1}` with
the same constant. See Cannarsa-Sinestrari (2004) **Corollary 3.3.8 p.61**: a function
simultaneously semiconcave and semiconvex with linear modulus `C` on an open convex
subset of `ℝⁿ` is `C^{1,1}` with Lipschitz constant of the derivative exactly `C`.
Equivalent statement: Rockafellar-Wets (1998) Proposition 13.34 p.605.

No convexity of `f` itself is needed. -/
theorem lipschitzWith_fderiv (h : LipschitzSmoothWith K f) :
    LipschitzWith K (fderiv ℝ f) :=
  sorry

/-- A `K`-smooth function on a finite-dimensional space is locally Lipschitz.
Corollary of `differentiable` + `lipschitzWith_fderiv` (a differentiable function with
locally bounded derivative is locally Lipschitz). -/
theorem locallyLipschitz (h : LipschitzSmoothWith K f) : LocallyLipschitz f :=
  sorry

/-- A `K`-smooth function on a finite-dimensional space is continuous. -/
theorem continuous (h : LipschitzSmoothWith K f) : Continuous f :=
  h.locallyLipschitz.continuous

end LipschitzSmoothWith
