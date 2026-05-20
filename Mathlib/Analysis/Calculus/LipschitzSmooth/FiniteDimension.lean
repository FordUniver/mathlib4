/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Lipschitz smoothness in finite-dimensional Hilbert spaces

In a finite-dimensional real inner-product space, `LipschitzSmoothWith K f` collapses
to the standard `C^{1,1}` class — Fréchet-differentiable with `K`-Lipschitz Fréchet
derivative — **without any convexity hypothesis on `f`**.

The route is via Cannarsa-Sinestrari's semiconcavity framework: the two-sided abs bound
on `lineDeriv` is equivalent to `f` being simultaneously `K`-semiconcave and `K`-semiconvex
with linear modulus. The translation between "K-semiconcave with linear modulus" and
"`f - K/2 ‖·‖²` concave" uses the parallelogram identity, so the proofs are stated in
a real inner-product space; the result extends to general finite-dim real normed spaces
via norm equivalence (deferred). Cannarsa-Sinestrari, *Semiconcave Functions,
Hamilton-Jacobi Equations, and Optimal Control* (2004), Corollary 3.3.8 (p.61) then
yields `f ∈ C^{1,1}` with the Lipschitz constant of `∇f` exactly `K`. An independent
route is Rockafellar-Wets, *Variational Analysis* (1998), Proposition 13.34 (p.605):
`C^{1+}` ⟺ lower-`C²` + upper-`C²`. Both proofs are finite-dim-essential.

The infinite-dim obstruction is genuine: a discontinuous linear functional `ℓ : F → ℝ`
satisfies `LipschitzSmoothWith 0 ℓ` but is not even continuous (Bauschke-Combettes,
*Convex Analysis and Monotone Operator Theory in Hilbert Spaces* (2017), Example 8.42
p.151). So the `[FiniteDimensional ℝ F]` hypothesis is not just convenient — it is
*necessary* in the absence of an explicit continuity or differentiability assumption.

## Main results

- `LipschitzSmoothWith.concaveOn_sub_half_sq_norm`: `f - K/2 ‖·‖²` is concave on the
  whole space (the semiconcavity decomposition, general dim).
- `LipschitzSmoothWith.differentiable`: `f` is Fréchet differentiable everywhere.
- `LipschitzSmoothWith.lipschitzWith_fderiv`: `fderiv ℝ f` is `K`-Lipschitz.
- `LipschitzSmoothWith.locallyLipschitz`: `f` is locally Lipschitz (corollary).
- `LipschitzSmoothWith.continuous`: `f` is continuous (corollary).

## Implementation notes

The semiconcavity decomposition (`concaveOn_sub_half_sq_norm`) holds in any real
inner-product space, regardless of dimension. The `Differentiable` / `LipschitzWith`
/ `LocallyLipschitz` / `Continuous` corollaries additionally require
`[FiniteDimensional ℝ F]` — without it, the discontinuous linear functional
counterexample obstructs continuity.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {K : NNReal} {f : F → ℝ}

namespace LipschitzSmoothWith

open scoped InnerProductSpace RealInnerProductSpace

/-- **Semiconcavity decomposition.** A `K`-smooth function `f` on a real inner-product
space makes `f - K/2 ‖·‖²` concave on the whole space.

The proof is the standard averaging argument: applying the predicate's upper-bound
direction at `(z, x)` and `(z, y)` with `z = a • x + b • y` (and `a + b = 1`),
the line-derivative terms cancel by positive homogeneity (since `x - z` and `y - z`
are anti-parallel scalar multiples of `x - y`), leaving the semiconcavity inequality
`a • f x + b • f y ≤ f z + K/2 · a b ‖x - y‖²`. The parallelogram identity
`a‖x‖² + b‖y‖² - ‖a•x + b•y‖² = a b ‖x - y‖²` (specific to inner-product spaces)
converts this to `ConcaveOn` form. -/
theorem concaveOn_sub_half_sq_norm (h : LipschitzSmoothWith K f) :
    ConcaveOn ℝ Set.univ (fun x : F => f x - ↑K / 2 * ‖x‖^2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set z : F := a • x + b • y with hz_def
  have hxz : x - z = b • (x - y) := by
    rw [hz_def]; match_scalars <;> linarith
  have hyz : y - z = (-a) • (x - y) := by
    rw [hz_def]; match_scalars <;> linarith
  have hux := h.lineDeriv_descent_le z x
  have huy := h.lineDeriv_descent_le z y
  rw [hxz, lineDeriv_smul, smul_eq_mul,
      show dist z x = b * ‖x - y‖ by
        rw [dist_eq_norm', hxz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb],
      mul_pow] at hux
  rw [hyz, lineDeriv_smul, smul_eq_mul,
      show dist z y = a * ‖x - y‖ by
        rw [dist_eq_norm', hyz, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ha],
      mul_pow] at huy
  -- Inner-product identity: a‖x‖² + b‖y‖² - ‖z‖² = a*b*‖x-y‖²
  have inner_id : a * ‖x‖^2 + b * ‖y‖^2 - ‖z‖^2 = a * b * ‖x - y‖^2 := by
    have e₁ : ‖z‖^2 = a^2 * ‖x‖^2 + 2 * (a * b) * ⟪x, y⟫_ℝ + b^2 * ‖y‖^2 := by
      rw [hz_def, @norm_add_sq_real F, norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, real_inner_smul_left,
        real_inner_smul_right]; ring
    have e₂ : ‖x - y‖^2 = ‖x‖^2 - 2 * ⟪x, y⟫_ℝ + ‖y‖^2 := @norm_sub_sq_real F _ _ _ _
    linear_combination -e₁ - a*b * e₂ - (a * ‖x‖^2 + b * ‖y‖^2) * hab
  -- Combine the two upper bounds; use linear_combination for the polynomial identities
  -- under hab and linarith for the final inequality.
  set L := lineDeriv ℝ f z (x - y) with hL_def
  set s := ‖x - y‖^2 with hs_def
  have hux' : a * f x ≤ a * f z + a * b * L + ↑K / 2 * (a * b^2 * s) := by
    have h1 := mul_le_mul_of_nonneg_left hux ha
    nlinarith [h1]
  have huy' : b * f y ≤ b * f z - a * b * L + ↑K / 2 * (b * a^2 * s) := by
    have h1 := mul_le_mul_of_nonneg_left huy hb
    nlinarith [h1]
  have coef_eq : a * b^2 + b * a^2 = a * b := by linear_combination a * b * hab
  have fz_eq : a * f z + b * f z = f z := by linear_combination f z * hab
  have rhs_eq :
      (a * f z + a * b * L + ↑K / 2 * (a * b^2 * s))
        + (b * f z - a * b * L + ↑K / 2 * (b * a^2 * s)) = f z + ↑K / 2 * (a * b * s) := by
    linear_combination fz_eq + (↑K / 2 * s) * coef_eq
  have sum_ineq : a * f x + b * f y ≤ f z + ↑K / 2 * (a * b * s) := by
    linarith [hux', huy', rhs_eq]
  have inner_id_K : ↑K / 2 * (a * ‖x‖^2 + b * ‖y‖^2 - ‖z‖^2) = ↑K / 2 * (a * b * s) := by
    linear_combination (↑K / 2) * inner_id
  have goal : a * (f x - ↑K / 2 * ‖x‖^2) + b * (f y - ↑K / 2 * ‖y‖^2) ≤
      f z - ↑K / 2 * ‖z‖^2 := by
    linarith [sum_ineq, inner_id_K]
  simpa using goal

end LipschitzSmoothWith

section FiniteDim

variable [FiniteDimensional ℝ F]

namespace LipschitzSmoothWith

/-- A `K`-smooth function on a finite-dim real inner-product space is locally Lipschitz.

Proof: the semiconcavity decomposition `f - K/2 ‖·‖²` concave (from
`concaveOn_sub_half_sq_norm`), combined with mathlib's
`ConcaveOn.locallyLipschitz` (which requires `[FiniteDimensional ℝ F]`), gives
local Lipschitz of the concave part. Adding back the locally Lipschitz `K/2 ‖·‖²`
recovers `f`. -/
theorem locallyLipschitz (h : LipschitzSmoothWith K f) : LocallyLipschitz f := by
  have hcon : LocallyLipschitz (fun x : F => f x - ↑K / 2 * ‖x‖^2) :=
    h.concaveOn_sub_half_sq_norm.locallyLipschitz
  have hquad : LocallyLipschitz (fun x : F => ↑K / 2 * ‖x‖^2) :=
    (contDiff_const.mul (contDiff_norm_sq (𝕜 := ℝ))).locallyLipschitz
  have heq : f = (fun x : F => f x - ↑K / 2 * ‖x‖^2) + fun x => ↑K / 2 * ‖x‖^2 := by
    funext x; simp only [Pi.add_apply]; ring
  rw [heq]
  exact hcon.add hquad

/-- A `K`-smooth function on a finite-dim real inner-product space is continuous. -/
theorem continuous (h : LipschitzSmoothWith K f) : Continuous f :=
  h.locallyLipschitz.continuous

/-- A `K`-smooth function on a finite-dim real inner-product space is Fréchet
differentiable everywhere. (sorry'd — proof via super-gradient sandwich.) -/
theorem differentiable (h : LipschitzSmoothWith K f) : Differentiable ℝ f :=
  sorry

/-- The Fréchet derivative of a `K`-smooth function on a finite-dim real inner-product
space is `K`-Lipschitz. (sorry'd — Cannarsa-Sinestrari 2004 Cor 3.3.8 p.61.) -/
theorem lipschitzWith_fderiv (h : LipschitzSmoothWith K f) :
    LipschitzWith K (fderiv ℝ f) :=
  sorry

end LipschitzSmoothWith

end FiniteDim
