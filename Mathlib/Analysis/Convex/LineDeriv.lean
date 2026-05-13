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

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function convex on `s`, where `x, y ∈ s`,
is convex on `Icc 0 1` (the segment from `x` to `y` lies in `s` by convexity of `s`). -/
theorem ConvexOn.lineRestriction (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (x + t • (y - x))) := by
  have heq : (fun t : ℝ => f (x + t • (y - x))) = f ∘ AffineMap.lineMap x y := by
    funext t
    change f (x + t • (y - x)) = f (AffineMap.lineMap x y t)
    rw [AffineMap.lineMap_apply_module', add_comm]
  rw [heq]
  refine (hc.comp_affineMap (AffineMap.lineMap x y)).subset (fun t ht => ?_)
    (convex_Icc _ _)
  exact hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function concave on `s`, where `x, y ∈ s`,
is concave on `Icc 0 1`. -/
theorem ConcaveOn.lineRestriction (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (x + t • (y - x))) := by
  have heq : (fun t : ℝ => f (x + t • (y - x))) = f ∘ AffineMap.lineMap x y := by
    funext t
    change f (x + t • (y - x)) = f (AffineMap.lineMap x y t)
    rw [AffineMap.lineMap_apply_module', add_comm]
  rw [heq]
  refine (hc.comp_affineMap (AffineMap.lineMap x y)).subset (fun t ht => ?_)
    (convex_Icc _ _)
  exact hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)

namespace ConvexOn

/-- For a convex function `f` line-differentiable at `x` in direction `y - x`,
the first-order inequality `f x + lineDeriv ℝ f x (y - x) ≤ f y` holds. -/
theorem add_lineDeriv_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f x + lineDeriv ℝ f x (y - x) ≤ f y := by
  -- Restrict to the line through `x` and `y`, then apply the 1D additive form.
  have hg_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (x + t • (y - x))) :=
    hc.lineRestriction hx hy
  have hg_deriv : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) (lineDeriv ℝ f x (y - x)) 0 :=
    hf.hasDerivAt
  have h := hg_conv.add_hasDerivAt_mul_le
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_lt_one hg_deriv
  simpa using h

/-- Monotonicity of the directional derivative along the chord: for convex `f`
line-differentiable at both endpoints in direction `y - x`,
`0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)`. -/
theorem lineDeriv_sub_apply_nonneg (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hfx : LineDifferentiableAt ℝ f x (y - x))
    (hfy : LineDifferentiableAt ℝ f y (y - x)) :
    0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) := by
  -- `f x + lineDeriv f x (y - x) ≤ f y` from `add_lineDeriv_le` at `(x, y)`.
  have h1 : f x + lineDeriv ℝ f x (y - x) ≤ f y :=
    hc.add_lineDeriv_le hx hy hfx
  -- For the symmetric bound at `(y, x)`, line-differentiability in direction `x - y`
  -- is equivalent to line-differentiability in direction `y - x` (smul by `-1`).
  have hfy' : LineDifferentiableAt ℝ f y (x - y) := by
    have : (x - y) = (-1 : ℝ) • (y - x) := by rw [neg_one_smul, neg_sub]
    rw [this]
    exact hfy.smul (-1)
  -- `f y + lineDeriv f y (x - y) ≤ f x` from `add_lineDeriv_le` at `(y, x)`.
  have h2 : f y + lineDeriv ℝ f y (x - y) ≤ f x :=
    hc.add_lineDeriv_le hy hx hfy'
  -- Rewrite `lineDeriv f y (x - y) = -lineDeriv f y (y - x)`.
  have h3 : lineDeriv ℝ f y (x - y) = -lineDeriv ℝ f y (y - x) := by
    rw [show (x - y) = -(y - x) from (neg_sub y x).symm, lineDeriv_neg]
  rw [h3] at h2
  linarith

end ConvexOn

namespace ConcaveOn

/-- For a concave function `f` line-differentiable at `x` in direction `y - x`,
the reverse first-order inequality `f y ≤ f x + lineDeriv ℝ f x (y - x)` holds. -/
theorem le_add_lineDeriv (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) := by
  -- Restrict to the line through `x` and `y`, then apply the 1D additive form for concave.
  have hg_conc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (x + t • (y - x))) :=
    hc.lineRestriction hx hy
  have hg_deriv : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) (lineDeriv ℝ f x (y - x)) 0 :=
    hf.hasDerivAt
  have h := hg_conc.le_add_hasDerivAt_mul
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_lt_one hg_deriv
  simpa using h

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
