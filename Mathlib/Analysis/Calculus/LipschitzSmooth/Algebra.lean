/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv
public import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap

/-!
# Algebraic preservation of Lipschitz smoothness

Closure properties of the `LipschitzSmoothWith` predicate under the standard algebraic
operations: pointwise addition (with `K₁ + K₂`), nonnegative scalar multiplication (with
`c · K`), and composition with continuous affine maps (with `‖A.contLinear‖² · K`).

The basic K = 0 cases for constants and affine functions live in
`Mathlib.Analysis.Calculus.LipschitzSmooth.Basic`. Note that `LipschitzSmoothWith` is *not*
closed under negation or negative scaling — the descent inequality is one-sided, mirroring
the asymmetry of concavity.
-/

public section

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
variable {K K₁ K₂ : NNReal} {f f₁ f₂ : F → ℝ}

/-- A continuous affine map `A : F →ᴬ[ℝ] ℝ` is `0`-smooth. Bundled form of
`lipschitzSmoothWith_affine` (which splits into linear part + constant). -/
theorem lipschitzSmoothWith_continuousAffineMap (A : F →ᴬ[ℝ] ℝ) :
    LipschitzSmoothWith (0 : NNReal) (A : F → ℝ) := by
  rw [show (A : F → ℝ) = ⇑A.contLinear + Function.const F (A 0) from A.decomp]
  exact lipschitzSmoothWith_affine A.contLinear (A 0)

namespace LipschitzSmoothWith

/-- Sum of `K₁`-smooth and `K₂`-smooth (differentiable) is `(K₁ + K₂)`-smooth. -/
theorem add (h₁ : LipschitzSmoothWith K₁ f₁) (h₂ : LipschitzSmoothWith K₂ f₂)
    (hf₁ : Differentiable ℝ f₁) (hf₂ : Differentiable ℝ f₂) :
    LipschitzSmoothWith (K₁ + K₂) (f₁ + f₂) := by
  rw [lipschitzSmoothWith_iff_fderiv (hf₁.add hf₂)]
  intro x y
  rw [fderiv_add (hf₁ x) (hf₂ x), ContinuousLinearMap.add_apply]
  have h1 := (lipschitzSmoothWith_iff_fderiv hf₁).mp h₁ x y
  have h2 := (lipschitzSmoothWith_iff_fderiv hf₂).mp h₂ x y
  push_cast
  simp only [Pi.add_apply]
  linarith

/-- Scaling a `K`-smooth (differentiable) function by `c : NNReal` gives `(c * K)`-smoothness. -/
theorem const_smul (h : LipschitzSmoothWith K f) (hf : Differentiable ℝ f) (c : NNReal) :
    LipschitzSmoothWith (c * K) ((c : ℝ) • f) := by
  have hcf : Differentiable ℝ ((c : ℝ) • f) := hf.const_smul (c : ℝ)
  rw [lipschitzSmoothWith_iff_fderiv hcf]
  intro x y
  rw [fderiv_const_smul (hf x) (c : ℝ), ContinuousLinearMap.smul_apply]
  have hd := (lipschitzSmoothWith_iff_fderiv hf).mp h x y
  push_cast
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith [c.coe_nonneg, sq_nonneg (dist x y)]

/-- Composition of a `K`-smooth `f : F → ℝ` with a continuous affine map `A : F' →ᴬ[ℝ] F`
is `(‖A.contLinear‖² · K)`-smooth on `F'`. -/
theorem comp_continuousAffineMap (h : LipschitzSmoothWith K f) (A : F' →ᴬ[ℝ] F) :
    LipschitzSmoothWith (‖A.contLinear‖₊ ^ 2 * K) (f ∘ A) :=
  sorry

end LipschitzSmoothWith
