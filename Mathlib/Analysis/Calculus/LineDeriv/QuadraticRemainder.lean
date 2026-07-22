/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Quadratic line remainders

We study functions whose first-order remainder from `lineDeriv` is bounded quadratically.
Such a bound ensures that the line derivative exists and is linear in its direction.

## Main definition

* `HasQuadraticLineRemainderWith`: the first-order remainder from `lineDeriv` is uniformly bounded
  by a quadratic function.

## Main results

* `HasQuadraticLineRemainderWith.hasLineDerivAt`: the line derivative actually exists.
* `HasQuadraticLineRemainderWith.norm_image_lineMap_sub_lineMap_le`: the function is approximately
  affine along lines.
* `HasQuadraticLineRemainderWith.isLinearMap_lineDeriv`: the line derivative is linear in its
  direction.
-/

public section

noncomputable section

open scoped NNReal Topology

open AffineMap Asymptotics Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {C : NNReal} {f : E → F}

variable (𝕜)

/-- `HasQuadraticLineRemainderWith 𝕜 C f` means that the first-order Taylor remainder from
`lineDeriv` is bounded by `C * dist x y ^ 2`, uniformly in `x` and `y`. -/
@[expose]
def HasQuadraticLineRemainderWith (C : NNReal) (f : E → F) : Prop :=
  ∀ x y, ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2

variable {𝕜}

namespace HasQuadraticLineRemainderWith

/-- A uniform quadratic bound on the remainder from `lineDeriv` ensures that `lineDeriv` is the
actual line derivative. -/
theorem hasLineDerivAt (h : HasQuadraticLineRemainderWith 𝕜 C f) (x v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v := by
  change HasDerivAt (fun t : 𝕜 ↦ f (x + t • v)) (lineDeriv 𝕜 f x v) 0
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (IsBigO.of_bound (C * ‖v‖ ^ 2) (Eventually.of_forall fun t ↦ ?_)).trans_isLittleO
    (isLittleO_pow_id one_lt_two)
  have ht := h x (x + t • v)
  rw [show (x + t • v) - x = t • v by abel, lineDeriv_smul,
    dist_self_add_right, norm_smul, mul_pow] at ht
  simpa only [zero_add, zero_smul, add_zero, norm_pow, mul_assoc, mul_left_comm, mul_comm] using ht

/-- A quadratic line remainder bound controls the failure of `f` to commute with affine
interpolation. -/
theorem norm_image_lineMap_sub_lineMap_le (h : HasQuadraticLineRemainderWith 𝕜 C f)
    (x y : E) (c : 𝕜) :
    ‖f (lineMap x y c) - lineMap (f x) (f y) c‖ ≤
      C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by
  let z := lineMap x y c
  have hzx : z - x = c • (y - x) := by simp [z, lineMap_apply_module']
  have hdist : dist x z = ‖c‖ * dist x y := by
    rw [dist_eq_norm, show x - z = c • (x - y) by
      simp [z, lineMap_apply_module]; module, norm_smul, dist_eq_norm]
  have hz : ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ ≤
      C * (‖c‖ ^ 2 * dist x y ^ 2) := by
    calc
      _ ≤ C * dist x z ^ 2 := h x z
      _ = _ := by rw [hdist, mul_pow]
  calc
    ‖f z - lineMap (f x) (f y) c‖ =
        ‖(f z - f x - lineDeriv 𝕜 f x (z - x)) -
          c • (f y - f x - lineDeriv 𝕜 f x (y - x))‖ := by
      congr 1
      rw [lineMap_apply_module, hzx, lineDeriv_smul]
      module
    _ ≤ ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ +
        ‖c • (f y - f x - lineDeriv 𝕜 f x (y - x))‖ := norm_sub_le _ _
    _ = ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ +
        ‖c‖ * ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ := by rw [norm_smul]
    _ ≤ C * (‖c‖ ^ 2 * dist x y ^ 2) + ‖c‖ * (C * dist x y ^ 2) :=
      add_le_add hz (mul_le_mul_of_nonneg_left (h x y) (norm_nonneg c))
    _ = C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by ring

/-- If the remainder from `lineDeriv` is uniformly bounded by a quadratic function, then the line
derivative is linear in the direction. -/
theorem isLinearMap_lineDeriv (h : HasQuadraticLineRemainderWith 𝕜 C f) (x : E) :
    IsLinearMap 𝕜 (lineDeriv 𝕜 f x) := by
  refine IsLinearMap.mk ?_ fun c v ↦ lineDeriv_smul
  intro u v
  obtain ⟨c : 𝕜, hc_pos, hc_lt⟩ := NormedField.exists_norm_lt_one 𝕜
  have hc : c ≠ 0 := norm_ne_zero_iff.mp hc_pos.ne'
  have h_one_sub_c : 1 - c ≠ 0 := by
    intro hc'
    have : c = 1 := (sub_eq_zero.mp hc').symm
    simp [this] at hc_lt
  let u' := (1 - c)⁻¹ • u
  let v' := c⁻¹ • v
  let q := (1 - c) • u' + c • v'
  have hq : q = u + v := by
    simp [q, u', v', h_one_sub_c, hc]
  suffices lineDeriv 𝕜 f x q =
      (1 - c) • lineDeriv 𝕜 f x u' + c • lineDeriv 𝕜 f x v' by
    simpa [hq, u', v', h_one_sub_c, hc, lineDeriv_smul] using this
  let g := fun t : 𝕜 ↦
    f (x + t • q) - ((1 - c) • f (x + t • u') + c • f (x + t • v'))
  have hg_deriv : HasDerivAt g
      (lineDeriv 𝕜 f x q -
        ((1 - c) • lineDeriv 𝕜 f x u' + c • lineDeriv 𝕜 f x v')) 0 :=
    (h.hasLineDerivAt x q).sub
      (((h.hasLineDerivAt x u').const_smul (1 - c)).add
        ((h.hasLineDerivAt x v').const_smul c))
  have hg_zero : g 0 = 0 := by
    simp only [g, zero_smul, add_zero]
    module
  have hg_bigO : g =O[𝓝 0] fun t : 𝕜 ↦ t ^ 2 := by
    refine IsBigO.of_bound
      (C * (‖c‖ ^ 2 + ‖c‖) * ‖v' - u'‖ ^ 2) (Eventually.of_forall fun t ↦ ?_)
    let a := x + t • u'
    let b := x + t • v'
    have hline : x + t • q = lineMap a b c := by
      simp [q, a, b, lineMap_apply_module]
      module
    have hdist : dist a b = ‖t‖ * ‖v' - u'‖ := by
      rw [dist_eq_norm]
      simp only [a, b, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, norm_sub_rev]
    have hg_eq : g t = f (lineMap a b c) - lineMap (f a) (f b) c := by
      simp only [g, a, b, hline, lineMap_apply_module]
    rw [hg_eq]
    refine (h.norm_image_lineMap_sub_lineMap_le a b c).trans_eq ?_
    rw [hdist, mul_pow, norm_pow]
    ring
  have hg_deriv_zero : HasDerivAt g 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa [hg_zero] using hg_bigO.trans_isLittleO (isLittleO_pow_id one_lt_two)
  exact sub_eq_zero.mp (hg_deriv.unique hg_deriv_zero)

end HasQuadraticLineRemainderWith
