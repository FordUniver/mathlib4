/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# First-order convexity inequality via the directional derivative

For `f : E → ℝ` convex on `s ⊆ E` and line-differentiable at `x ∈ s` in the direction
`y - x`, the first-order convexity inequality

`f x + lineDeriv ℝ f x (y - x) ≤ f y`

holds for `y ∈ s`. This is the directional-derivative form of the convex subgradient
inequality, lifted from the 1D case in `Mathlib.Analysis.Convex.Deriv` by restricting
to the line segment between `x` and `y`.

## Main results

* `ConvexOn.add_lineDeriv_le` — the first-order convexity inequality (line-derivative
  form).
* `ConcaveOn.le_add_lineDeriv` — the concave dual.
* `ConvexOn.lineDeriv_sub_apply_nonneg` — monotonicity of the directional derivative:
  `0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)`.
* `StrictConvexOn.add_lineDeriv_lt` — strict variant under `StrictConvexOn`.
* `convexOn_iff_add_lineDeriv_le` — iff converse: line-differentiability everywhere plus
  the first-order inequality implies `ConvexOn`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {s : Set E} {x y : E}

namespace ConvexOn

/-- For a convex function `f` line-differentiable at `x` in direction `y - x`,
the first-order inequality `f x + lineDeriv ℝ f x (y - x) ≤ f y` holds. -/
theorem add_lineDeriv_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f x + lineDeriv ℝ f x (y - x) ≤ f y := by
  sorry

/-- Monotonicity of the directional derivative along the chord: for convex `f`
line-differentiable at both endpoints in direction `y - x`,
`0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)`. -/
theorem lineDeriv_sub_apply_nonneg (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hfx : LineDifferentiableAt ℝ f x (y - x))
    (hfy : LineDifferentiableAt ℝ f y (y - x)) :
    0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) := by
  sorry

end ConvexOn

namespace ConcaveOn

/-- For a concave function `f` line-differentiable at `x` in direction `y - x`,
the reverse first-order inequality `f y ≤ f x + lineDeriv ℝ f x (y - x)` holds. -/
theorem le_add_lineDeriv (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) := by
  sorry

end ConcaveOn

namespace StrictConvexOn

/-- Strict variant of the first-order inequality for strictly convex `f`:
when `x ≠ y`, the inequality is strict. -/
theorem add_lineDeriv_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f x + lineDeriv ℝ f x (y - x) < f y := by
  sorry

end StrictConvexOn

/-- A line-differentiable function is convex iff it satisfies the first-order inequality
at every pair of points in `s`. -/
theorem convexOn_iff_add_lineDeriv_le (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, ∀ y ∈ s, LineDifferentiableAt ℝ f x (y - x)) :
    ConvexOn ℝ s f ↔
      ∀ x ∈ s, ∀ y ∈ s, f x + lineDeriv ℝ f x (y - x) ≤ f y := by
  sorry
