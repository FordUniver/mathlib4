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
`c · K`), and composition with continuous affine maps (with `‖A.contLinear‖² · K`). The
two-sided abs-form of the predicate also makes it closed under negation (same `K`) and so
under scaling by arbitrary real `c` (with `|c| · K`).

The basic K = 0 cases for constants and affine functions live in
`Mathlib.Analysis.Calculus.LipschitzSmooth.Basic`. None of the lemmas here require any
differentiability hypothesis — `LipschitzSmoothWith` implies line-differentiability
everywhere via `LipschitzSmoothWith.hasLineDerivAt`.
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

/-- Sum of `K₁`-smooth and `K₂`-smooth is `(K₁ + K₂)`-smooth. No differentiability hypothesis
needed: each summand is line-differentiable everywhere (`hasLineDerivAt`), so the sum is too,
with line-derivative the sum of line-derivatives. -/
theorem add (h₁ : LipschitzSmoothWith K₁ f₁) (h₂ : LipschitzSmoothWith K₂ f₂) :
    LipschitzSmoothWith (K₁ + K₂) (f₁ + f₂) := lipschitzSmoothWith_iff_lineDeriv.mpr fun x y => by
  have hd : HasLineDerivAt ℝ (f₁ + f₂)
      (lineDeriv ℝ f₁ x (y - x) + lineDeriv ℝ f₂ x (y - x)) x (y - x) :=
    HasDerivAt.add (h₁.hasLineDerivAt x (y - x)) (h₂.hasLineDerivAt x (y - x))
  rw [hd.lineDeriv]
  have h1 := h₁.lineDeriv_abs_le x y
  have h2 := h₂.lineDeriv_abs_le x y
  calc |(f₁ + f₂) y - (f₁ + f₂) x - (lineDeriv ℝ f₁ x (y - x) + lineDeriv ℝ f₂ x (y - x))|
      = |(f₁ y - f₁ x - lineDeriv ℝ f₁ x (y - x))
          + (f₂ y - f₂ x - lineDeriv ℝ f₂ x (y - x))| := by
        simp only [Pi.add_apply]; ring_nf
    _ ≤ |f₁ y - f₁ x - lineDeriv ℝ f₁ x (y - x)|
        + |f₂ y - f₂ x - lineDeriv ℝ f₂ x (y - x)| := abs_add_le _ _
    _ ≤ ↑(K₁ + K₂) / 2 * (dist x y) ^ 2 := by push_cast; linarith

/-- Negation preserves `K`-smoothness with the same constant. Trivial under the two-sided
abs form of the predicate. -/
theorem neg (h : LipschitzSmoothWith K f) : LipschitzSmoothWith K (-f) :=
    lipschitzSmoothWith_iff_lineDeriv.mpr fun x y => by
  have hd : HasLineDerivAt ℝ (-f) (-lineDeriv ℝ f x (y - x)) x (y - x) :=
    HasDerivAt.neg (h.hasLineDerivAt x (y - x))
  rw [hd.lineDeriv]
  have habs := h.lineDeriv_abs_le x y
  rw [show ((-f) y - (-f) x - -lineDeriv ℝ f x (y - x))
      = -(f y - f x - lineDeriv ℝ f x (y - x)) from by simp; ring, abs_neg]
  exact habs

/-- Scaling a `K`-smooth function by `c : NNReal` gives `(c * K)`-smoothness. No
differentiability hypothesis needed: line-differentiability follows from `hasLineDerivAt`. -/
theorem const_smul (h : LipschitzSmoothWith K f) (c : NNReal) :
    LipschitzSmoothWith (c * K) ((c : ℝ) • f) := lipschitzSmoothWith_iff_lineDeriv.mpr fun x y => by
  have hd : HasLineDerivAt ℝ ((c : ℝ) • f) ((c : ℝ) • lineDeriv ℝ f x (y - x)) x (y - x) :=
    (h.hasLineDerivAt x (y - x)).const_smul (c : ℝ)
  rw [hd.lineDeriv]
  have habs := h.lineDeriv_abs_le x y
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  calc |((c : ℝ) • f) y - ((c : ℝ) • f) x - (c : ℝ) • lineDeriv ℝ f x (y - x)|
      = (c : ℝ) * |f y - f x - lineDeriv ℝ f x (y - x)| := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [show (c : ℝ) * f y - (c : ℝ) * f x - (c : ℝ) * lineDeriv ℝ f x (y - x)
            = (c : ℝ) * (f y - f x - lineDeriv ℝ f x (y - x)) from by ring,
          abs_mul, abs_of_nonneg hc]
    _ ≤ ↑(c * K) / 2 * (dist x y) ^ 2 := by
        push_cast
        nlinarith [sq_nonneg (dist x y), K.coe_nonneg]

/-- Composition of a `K`-smooth `f : F → ℝ` with a continuous affine map `A : F' →ᴬ[ℝ] F`
is `(‖A.contLinear‖² · K)`-smooth on `F'`. -/
theorem comp_continuousAffineMap (h : LipschitzSmoothWith K f) (A : F' →ᴬ[ℝ] F) :
    LipschitzSmoothWith (‖A.contLinear‖₊ ^ 2 * K) (f ∘ A) :=
  sorry

end LipschitzSmoothWith
