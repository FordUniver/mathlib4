/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness in 1D via the derivative

For a `K`-smooth function `f : ℝ → ℝ`, the descent inequality and the variation bound
on the derivative take their classical 1D forms

`f y ≤ f x + deriv f x * (y - x) + K/2 * (y - x)^2`,
`(deriv f y - deriv f x) * (y - x) ≤ K * (y - x)^2`.

These are the 1D restatements of the Fréchet-derivative forms in
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv`, lifted via `fderiv_eq_deriv_mul`
(the identity `(fderiv ℝ f x : ℝ → ℝ) y = deriv f x * y`).

## Main results

* `lipschitzSmoothWith_iff_deriv` — characterisation in 1D `deriv` form under `Differentiable`.
* `LipschitzSmoothWith.deriv_descent_le`, `LipschitzSmoothWith.deriv_sub_mul_le` —
  the descent inequality and the variance bound on the 1D `deriv`.
* `lipschitzWith_fderiv_iff_lipschitzWith_deriv` — for `f : ℝ → ℝ`, the Lipschitz
  constants of `fderiv ℝ f` and `deriv f` coincide.
* `Differentiable.lipschitzSmoothWith_of_lipschitzWith_deriv` — descent lemma in 1D:
  a function with `K`-Lipschitz `deriv` is `K`-smooth.
-/

public section

variable {K : NNReal} {f : ℝ → ℝ}

theorem lipschitzSmoothWith_iff_deriv (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔
      ∀ x y : ℝ, f y ≤ f x + deriv f x * (y - x) + ↑K / 2 * (y - x) ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv hf]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [fderiv_eq_deriv_mul, dist_comm, Real.dist_eq, sq_abs]

namespace LipschitzSmoothWith

theorem deriv_descent_le (h : LipschitzSmoothWith K f) (x y : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + deriv f x * (y - x) + ↑K / 2 * (y - x) ^ 2 := by
  have hbase := h.fderiv_descent_le x y hf
  rwa [fderiv_eq_deriv_mul, dist_comm, Real.dist_eq, sq_abs] at hbase

theorem deriv_sub_mul_le (h : LipschitzSmoothWith K f) (x y : ℝ)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    (deriv f y - deriv f x) * (y - x) ≤ ↑K * (y - x) ^ 2 := by
  have hbase := h.fderiv_sub_apply_le x y hfx hfy
  rwa [ContinuousLinearMap.sub_apply, fderiv_eq_deriv_mul, fderiv_eq_deriv_mul, ← sub_mul,
    dist_comm, Real.dist_eq, sq_abs] at hbase

end LipschitzSmoothWith

/-! ### Descent lemma in 1D -/

/-- For `f : ℝ → ℝ`, the Lipschitz constants of `fderiv ℝ f` and `deriv f` coincide.
The isomorphism `r ↦ smulRight 1 r : ℝ → ℝ →L[ℝ] ℝ` is an isometry, so Lipschitz
properties transfer between the two views of the derivative. -/
theorem lipschitzWith_fderiv_iff_lipschitzWith_deriv :
    LipschitzWith K (fderiv ℝ f) ↔ LipschitzWith K (deriv f) := by
  have h : ∀ x y : ℝ, fderiv ℝ f x - fderiv ℝ f y =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv f x - deriv f y) := fun x y => by
    ext
    rw [ContinuousLinearMap.sub_apply, fderiv_eq_deriv_mul, fderiv_eq_deriv_mul,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
    ring
  simp_rw [lipschitzWith_iff_dist_le_mul, dist_eq_norm]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [h x y, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]

/-- **Descent lemma (1D).** If `f : ℝ → ℝ` is differentiable and its derivative is
`K`-Lipschitz, then `f` is `K`-smooth. -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith_deriv
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (deriv f)) : LipschitzSmoothWith K f :=
  hf.lipschitzSmoothWith_of_lipschitzWith (lipschitzWith_fderiv_iff_lipschitzWith_deriv.mpr hL)
