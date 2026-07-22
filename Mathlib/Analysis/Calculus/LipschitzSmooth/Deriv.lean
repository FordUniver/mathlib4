/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness in one dimension

For `f : 𝕜 → F`, the Fréchet-derivative formulation of Lipschitz smoothness reduces to the
usual derivative bound

`‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2`.
-/

public section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : 𝕜 → F} {s : Set 𝕜}

theorem lipschitzSmoothOnWith_iff_deriv :
    LipschitzSmoothOnWith 𝕜 K f s ↔
      (∀ x ∈ s, DifferentiableAt 𝕜 f x) ∧
        ∀ x ∈ s, ∀ y ∈ s,
          ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothOnWith_iff_fderiv]
  refine and_congr_right fun _ ↦ ?_
  simp only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev]

theorem lipschitzSmoothWith_iff_deriv :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y : 𝕜,
        ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv_norm_le]
  simp only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev]

namespace LipschitzSmoothOnWith

theorem deriv_norm_le (h : LipschitzSmoothOnWith 𝕜 K f s)
    {x : 𝕜} (hx : x ∈ s) {y : 𝕜} (hy : y ∈ s) :
    ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  (lipschitzSmoothOnWith_iff_deriv.mp h).2 x hx y hy

end LipschitzSmoothOnWith

namespace LipschitzSmoothWith

theorem deriv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : 𝕜) :
    ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  lipschitzSmoothWith_iff_deriv.mp h x y

end LipschitzSmoothWith

/-! ### Real-valued functions -/

namespace LipschitzSmoothOnWith

variable {K : NNReal} {f : ℝ → ℝ} {s : Set ℝ}

theorem deriv_descent_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : ℝ} (hx : x ∈ s) {y : ℝ} (hy : y ∈ s) :
    f y ≤ f x + deriv f x * (y - x) + K / 2 * (y - x) ^ 2 := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_le hx hy

theorem deriv_descent_ge (h : LipschitzSmoothOnWith ℝ K f s)
    {x : ℝ} (hx : x ∈ s) {y : ℝ} (hy : y ∈ s) :
    f x + deriv f x * (y - x) - K / 2 * (y - x) ^ 2 ≤ f y := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_ge hx hy

theorem deriv_sub_mul_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : ℝ} (hx : x ∈ s) {y : ℝ} (hy : y ∈ s) :
    (deriv f y - deriv f x) * (y - x) ≤ K * (y - x) ^ 2 := by
  simpa only [sub_apply, fderiv_eq_deriv_mul, ← sub_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_sub_apply_le hx hy

end LipschitzSmoothOnWith

namespace LipschitzSmoothWith

variable {K : NNReal} {f : ℝ → ℝ}

theorem deriv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    f y ≤ f x + deriv f x * (y - x) + K / 2 * (y - x) ^ 2 := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_le x y

theorem deriv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    f x + deriv f x * (y - x) - K / 2 * (y - x) ^ 2 ≤ f y := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_ge x y

theorem deriv_sub_mul_le (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    (deriv f y - deriv f x) * (y - x) ≤ K * (y - x) ^ 2 := by
  simpa only [sub_apply, fderiv_eq_deriv_mul, ← sub_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_sub_apply_le x y

end LipschitzSmoothWith
