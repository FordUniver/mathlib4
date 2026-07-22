/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness on a Hilbert space via the gradient

On a Hilbert space `F`, Lipschitz smoothness admits a gradient-form characterisation. The identity
`fderiv ℝ f x (y - x) = ⟪∇ f x, y - x⟫` follows from Riesz representation, and the two-sided
Taylor bound becomes

`‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2`.

This file also defines the `CocoerciveWith K f` predicate, the conclusion of the Baillon-Haddad
theorem, and proves the elementary implication from `K`-cocoercivity to a `K`-Lipschitz gradient.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open scoped Gradient RealInnerProductSpace

theorem lipschitzSmoothWith_iff_inner_gradient :
    LipschitzSmoothWith ℝ K f ↔
      ∀ x y : F, ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv]
  simp only [inner_gradient_left, dist_eq_norm']

theorem lipschitzSmoothOnWith_iff_inner_gradientWithin {s : Set F}
    (hs : UniqueDiffOn ℝ s) :
    LipschitzSmoothOnWith ℝ K f s ↔ DifferentiableOn ℝ f s ∧
      ∀ x ∈ s, ∀ y ∈ s,
        ‖f y - f x - ⟪gradientWithin f s x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothOnWith_iff_fderivWithin hs]
  simp only [inner_gradientWithin_left, dist_eq_norm']

namespace LipschitzSmoothWith

theorem inner_gradient_norm_le (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  lipschitzSmoothWith_iff_inner_gradient.mp h x y

theorem inner_gradient_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    f y ≤ f x + ⟪∇ f x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2 := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_le x y

theorem inner_gradient_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    f x + ⟪∇ f x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_ge x y

theorem inner_gradient_sub_le (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    ⟪∇ f y - ∇ f x, y - x⟫ ≤ K * ‖y - x‖ ^ 2 := by
  simp only [← dist_eq_norm', inner_sub_left, inner_gradient_left, ← sub_apply]
  exact h.fderiv_sub_apply_le x y

end LipschitzSmoothWith

namespace LipschitzSmoothOnWith

variable {s : Set F}

/-- The defining within-set quadratic bound in terms of `gradientWithin`. -/
theorem inner_gradientWithin_norm_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : F} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - ⟪gradientWithin f s x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  (lipschitzSmoothOnWith_iff_inner_gradientWithin hs).mp h |>.2 x hx y hy

/-- The quadratic upper bound on `f y` within a set, in terms of `gradientWithin`. -/
theorem inner_gradientWithin_descent_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : F} (hx : x ∈ s) (hy : y ∈ s) :
    f y ≤ f x + ⟪gradientWithin f s x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2 := by
  rw [inner_gradientWithin_left, ← dist_eq_norm']
  exact h.fderivWithin_descent_le hs hx hy

/-- The quadratic lower bound on `f y` within a set, in terms of `gradientWithin`. -/
theorem inner_gradientWithin_descent_ge (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : F} (hx : x ∈ s) (hy : y ∈ s) :
    f x + ⟪gradientWithin f s x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  rw [inner_gradientWithin_left, ← dist_eq_norm']
  exact h.fderivWithin_descent_ge hs hx hy

/-- One-sided bound on the variation of `gradientWithin`. -/
theorem inner_gradientWithin_sub_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : F} (hx : x ∈ s) (hy : y ∈ s) :
    ⟪gradientWithin f s y - gradientWithin f s x, y - x⟫ ≤ K * ‖y - x‖ ^ 2 := by
  simp only [← dist_eq_norm', inner_sub_left, inner_gradientWithin_left, ← sub_apply]
  exact h.fderivWithin_sub_apply_le hs hx hy

end LipschitzSmoothOnWith

/-! ### Cocoercivity -/

/-- A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x`, `y`. This is equivalent to the
standard `(1/K) · ‖·‖² ≤ ⟪·, ·⟫` form when `0 < K`, but remains meaningful at `K = 0`.
This is the conclusion of the Baillon-Haddad theorem. -/
def CocoerciveWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫

theorem cocoerciveWith_iff :
    CocoerciveWith K f ↔
      ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫ :=
  Iff.rfl

namespace CocoerciveWith

/-- The defining cocoercivity bound. -/
theorem norm_sq_le (h : CocoerciveWith K f) (x y : F) :
    ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫ :=
  h x y

/-- A `K`-cocoercive gradient is `K`-Lipschitz. The reverse implication requires convexity. -/
theorem lipschitzWith_gradient (h : CocoerciveWith K f) : LipschitzWith K (∇ f) :=
  lipschitzWith_iff_dist_le_mul.mpr fun x y => by
    simp only [dist_eq_norm']
    nlinarith [h.norm_sq_le x y, mul_nonneg K.coe_nonneg (norm_nonneg (y - x)),
      mul_le_mul_of_nonneg_left (real_inner_le_norm (∇ f y - ∇ f x) (y - x)) K.coe_nonneg]

end CocoerciveWith
