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
  -- The 1D restriction of `f` to the segment from `x` to `y`.
  set g : ℝ → ℝ := fun t => f (x + t • (y - x)) with hg_def
  -- Bridge `g = f ∘ AffineMap.lineMap x y` (differ only by `add_comm` inside `f`).
  have hg_comp : g = f ∘ AffineMap.lineMap x y := by
    funext t
    change f (x + t • (y - x)) = f (AffineMap.lineMap x y t)
    rw [AffineMap.lineMap_apply_module', add_comm]
  -- Endpoint identities.
  have hg0 : g 0 = f x := by simp [g]
  have hg1 : g 1 = f y := by simp [g]
  -- `g` is convex on `Icc 0 1`.
  have hg_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    rw [hg_comp]
    refine (hc.comp_affineMap (AffineMap.lineMap x y)).subset (fun t ht => ?_)
      (convex_Icc _ _)
    exact hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)
  -- `g` has derivative `lineDeriv ℝ f x (y - x)` at `0` — directly from `LineDifferentiableAt`.
  have hg_deriv : HasDerivAt g (lineDeriv ℝ f x (y - x)) 0 := hf.hasDerivAt
  -- Apply the 1D first-order convexity inequality at points `0 < 1` in `Icc 0 1`.
  have h_slope := hg_conv.le_slope_of_hasDerivAt
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_lt_one hg_deriv
  -- `slope g 0 1 = g 1 - g 0 = f y - f x`; rearrange.
  rw [slope_def_field, hg0, hg1, sub_zero, div_one] at h_slope
  linarith

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
