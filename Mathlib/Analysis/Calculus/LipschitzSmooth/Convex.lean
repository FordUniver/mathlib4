/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.Gradient
public import Mathlib.Analysis.Convex.Function

/-!
# Convex Lipschitz-smooth functions and the Baillon-Haddad theorem

For a differentiable convex function on a Hilbert space, the following are equivalent:

* `LipschitzSmoothWith K f` — the quadratic descent inequality (`K`-smoothness)
* `LipschitzWith K (fderiv ℝ f)` — the Fréchet derivative is `K`-Lipschitz
* `LipschitzWith K (∇ f)` — the gradient is `K`-Lipschitz
* `CocoerciveWith K f` — `K`-cocoercivity of the gradient

The non-convex direction (`LipschitzWith K (fderiv ℝ f) → LipschitzSmoothWith K f`)
was established as the descent lemma in
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv`. The non-convex direction
`CocoerciveWith K f → LipschitzWith K (∇ f)` was established in
`Mathlib.Analysis.Calculus.LipschitzSmooth.Gradient`. This file establishes the
converse implications under `ConvexOn ℝ Set.univ f`, all of which follow from a
single atomic statement, the Baillon-Haddad theorem
(`ConvexOn.cocoerciveWith_of_lipschitzSmoothWith`).

## Main results

* `ConvexOn.cocoerciveWith_of_lipschitzSmoothWith` — **Baillon-Haddad theorem**:
  a differentiable convex `K`-smooth function on a Hilbert space is `K`-cocoercive.
* `ConvexOn.lipschitzSmoothWith_iff_cocoerciveWith`,
  `ConvexOn.lipschitzSmoothWith_iff_lipschitzWith_gradient`,
  `ConvexOn.lipschitzSmoothWith_iff_lipschitzWith_fderiv`,
  `ConvexOn.cocoerciveWith_iff_lipschitzWith_gradient` — the four pairwise equivalences
  under `ConvexOn ℝ Set.univ f`.
-/

public section

namespace ConvexOn

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open InnerProductSpace
open scoped Gradient RealInnerProductSpace

/-- **Baillon-Haddad theorem.** A differentiable convex `K`-smooth function on a Hilbert
space is `K`-cocoercive.

The standard proof: define `φₓ(z) := f(z) - ⟨∇f(x), z⟩`, which is convex and `K`-smooth
with minimum at `x` (since `∇φₓ(x) = 0`). Apply the descent inequality of `φₓ` at `y`
stepping by `-∇φₓ(y) / K`; using `φₓ(x) = min φₓ` yields
`‖∇f(y) - ∇f(x)‖² ≤ 2K (f(y) - f(x) - ⟨∇f(x), y - x⟩)`. Sum with the symmetric bound from
`φᵧ`, and the linear terms in `f` cancel to give the cocoercive inequality. -/
theorem cocoerciveWith_of_lipschitzSmoothWith
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (hs : LipschitzSmoothWith K f) : CocoerciveWith K f :=
  sorry

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to `K`-cocoercivity. The forward direction is the Baillon-Haddad theorem; the backward
direction goes via `K`-Lipschitz gradient and the descent lemma, no convexity needed. -/
theorem lipschitzSmoothWith_iff_cocoerciveWith
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ CocoerciveWith K f :=
  ⟨hc.cocoerciveWith_of_lipschitzSmoothWith hf,
    fun h => hf.lipschitzSmoothWith_of_lipschitzWith_gradient h.lipschitzWith_gradient⟩

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to `K`-Lipschitz gradient. Forward: K-smooth → cocoercive (Baillon-Haddad) → Lipschitz
gradient. Backward: the descent lemma in Hilbert form. -/
theorem lipschitzSmoothWith_iff_lipschitzWith_gradient
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ LipschitzWith K (∇ f) :=
  ⟨fun hs => (hc.cocoerciveWith_of_lipschitzSmoothWith hf hs).lipschitzWith_gradient,
    hf.lipschitzSmoothWith_of_lipschitzWith_gradient⟩

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to a `K`-Lipschitz Fréchet derivative. -/
theorem lipschitzSmoothWith_iff_lipschitzWith_fderiv
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ LipschitzWith K (fderiv ℝ f) :=
  (hc.lipschitzSmoothWith_iff_lipschitzWith_gradient hf).trans
    lipschitzWith_fderiv_iff_lipschitzWith_gradient.symm

/-- **Baillon-Haddad theorem** (`iff` form): for a differentiable convex function on a Hilbert
space, `K`-Lipschitz gradient is equivalent to `K`-cocoercivity. -/
theorem cocoerciveWith_iff_lipschitzWith_gradient
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    CocoerciveWith K f ↔ LipschitzWith K (∇ f) :=
  (hc.lipschitzSmoothWith_iff_cocoerciveWith hf).symm.trans
    (hc.lipschitzSmoothWith_iff_lipschitzWith_gradient hf)

end ConvexOn
