/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Quantitative consequences of Lipschitz smoothness

This file develops the quantitative Fréchet-derivative API for `LipschitzSmoothOnWith` and
`LipschitzSmoothWith`: variation bounds for the derivative and, for real-valued functions, the
upper and lower quadratic bounds usually called the descent lemma and, sometimes, the ascent
lemma.
-/

public section

open Asymptotics Filter
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F} {s : Set E}

namespace LipschitzSmoothWith

/-- A global quadratic bound written using `fderiv` already forces Fréchet differentiability,
and hence gives Lipschitz smoothness. -/
theorem of_fderiv_norm_le
    (h : ∀ x y : E,
      ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2) :
    LipschitzSmoothWith 𝕜 K f := by
  apply (lipschitzSmoothWith_iff_fderiv 𝕜).mpr
  refine ⟨fun x ↦ ?_, h⟩
  refine (HasFDerivAt.of_isLittleO (f' := fderiv 𝕜 f x) ?_).differentiableAt
  have hbigO : (fun y ↦ f y - f x - fderiv 𝕜 f x (y - x)) =O[𝓝 x]
      fun y ↦ ‖y - x‖ ^ 2 := by
    refine IsBigO.of_bound (K / 2) (Eventually.of_forall fun y ↦ ?_)
    simpa only [dist_eq_norm, norm_sub_rev, Real.norm_of_nonneg (sq_nonneg _)] using h x y
  exact hbigO.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

end LipschitzSmoothWith

/-- The explicit differentiability field in `LipschitzSmoothWith` is mathematically redundant:
the global quadratic `fderiv` bound already implies it. -/
theorem lipschitzSmoothWith_iff_fderiv_norm_le :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y : E,
        ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  ⟨fun h ↦ h.fderiv_norm_le, LipschitzSmoothWith.of_fderiv_norm_le⟩

namespace LipschitzSmoothOnWith

/-- Two-sided bound on the variation of the Fréchet derivative along `y - x`. -/
theorem fderiv_apply_sub_norm_le (h : LipschitzSmoothOnWith 𝕜 K f s)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    ‖fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x)‖ ≤ K * dist x y ^ 2 := by
  have hyx := h.fderiv_norm_le hy hx
  rw [← neg_sub y x, map_neg, sub_neg_eq_add, dist_comm] at hyx
  have hsum := (norm_add_le _ _).trans (add_le_add hyx (h.fderiv_norm_le hx hy))
  rw [show f x - f y + fderiv 𝕜 f y (y - x) +
      (f y - f x - fderiv 𝕜 f x (y - x)) =
        fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x) by abel] at hsum
  linarith

end LipschitzSmoothOnWith

namespace LipschitzSmoothWith

/-- Two-sided bound on the variation of the Fréchet derivative along `y - x`. -/
theorem fderiv_apply_sub_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x)‖ ≤ K * dist x y ^ 2 :=
  (h.lipschitzSmoothOnWith Set.univ).fderiv_apply_sub_norm_le (Set.mem_univ x) (Set.mem_univ y)

end LipschitzSmoothWith

/-! ### Real-valued functions -/

namespace LipschitzSmoothOnWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : NNReal} {f : E → ℝ} {s : Set E}

/-- The quadratic upper bound on `f y`, traditionally called the *descent lemma*. -/
theorem fderiv_descent_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    f y ≤ f x + fderiv ℝ f x (y - x) + K / 2 * dist x y ^ 2 := by
  linarith [(abs_le.mp (h.fderiv_norm_le hx hy)).2]

/-- The quadratic lower bound on `f y`, sometimes referred to as the *ascent lemma*. -/
theorem fderiv_descent_ge (h : LipschitzSmoothOnWith ℝ K f s)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    f x + fderiv ℝ f x (y - x) - K / 2 * dist x y ^ 2 ≤ f y := by
  linarith [(abs_le.mp (h.fderiv_norm_le hx hy)).1]

/-- One-sided bound on the variation of the Fréchet derivative along `y - x`. -/
theorem fderiv_apply_sub_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ K * dist x y ^ 2 :=
  le_of_abs_le (h.fderiv_apply_sub_norm_le hx hy)

/-- The one-sided variation bound in functional form. -/
theorem fderiv_sub_apply_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ K * dist x y ^ 2 := by
  rw [sub_apply]
  exact h.fderiv_apply_sub_le hx hy

end LipschitzSmoothOnWith

namespace LipschitzSmoothWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : NNReal} {f : E → ℝ}

/-- The quadratic upper bound on `f y`, traditionally called the *descent lemma*. -/
theorem fderiv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f y ≤ f x + fderiv ℝ f x (y - x) + K / 2 * dist x y ^ 2 :=
  (h.lipschitzSmoothOnWith Set.univ).fderiv_descent_le (Set.mem_univ x) (Set.mem_univ y)

/-- The quadratic lower bound on `f y`, sometimes referred to as the *ascent lemma*. -/
theorem fderiv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f x + fderiv ℝ f x (y - x) - K / 2 * dist x y ^ 2 ≤ f y :=
  (h.lipschitzSmoothOnWith Set.univ).fderiv_descent_ge (Set.mem_univ x) (Set.mem_univ y)

/-- One-sided bound on the variation of the Fréchet derivative along `y - x`. -/
theorem fderiv_apply_sub_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ K * dist x y ^ 2 :=
  (h.lipschitzSmoothOnWith Set.univ).fderiv_apply_sub_le (Set.mem_univ x) (Set.mem_univ y)

/-- The one-sided variation bound in functional form. -/
theorem fderiv_sub_apply_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ K * dist x y ^ 2 :=
  (h.lipschitzSmoothOnWith Set.univ).fderiv_sub_apply_le (Set.mem_univ x) (Set.mem_univ y)

end LipschitzSmoothWith
