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

## Main definitions

* `HasQuadraticLineRemainderWith`: the first-order remainder from `lineDeriv` is uniformly bounded
  by a quadratic function.
* `HasQuadraticLineRemainderWithAt`: the same bound holds uniformly for pairs of points in a
  neighborhood of a given point.

## Main results

* `HasQuadraticLineRemainderWithAt.hasLineDerivAt`: the line derivative actually exists.
* `HasQuadraticLineRemainderWithAt.lineDerivLinearMap`: the line derivative bundled as a linear
  map in its direction.
* `HasQuadraticLineRemainderWithAt.differentiableAt_iff_continuousAt`: under a local quadratic
  remainder bound, Fréchet differentiability is equivalent to continuity.
-/

public section

noncomputable section

open scoped NNReal Topology

open AffineMap Asymptotics Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {C : NNReal} {f : E → F} {x : E}

variable (𝕜)

/-- `HasQuadraticLineRemainderWith 𝕜 C f` means that the first-order Taylor remainder from
`lineDeriv` is bounded by `C * dist x y ^ 2`, uniformly in `x` and `y`. -/
@[expose]
def HasQuadraticLineRemainderWith (C : NNReal) (f : E → F) : Prop :=
  ∀ x y, ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2

/-- `HasQuadraticLineRemainderWithAt 𝕜 C f x` means that the first-order Taylor remainder from
`lineDeriv` is bounded by `C * dist y z ^ 2` for all pairs `y`, `z` in some neighborhood of `x`.
-/
@[expose]
def HasQuadraticLineRemainderWithAt (C : NNReal) (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, ∀ y ∈ s, ∀ z ∈ s,
    ‖f z - f y - lineDeriv 𝕜 f y (z - y)‖ ≤ C * dist y z ^ 2

variable {𝕜}

private theorem norm_image_lineMap_sub_lineMap_le_of_mem {s : Set E}
    (h : ∀ x ∈ s, ∀ y ∈ s,
      ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) (c : 𝕜) (hz : lineMap x y c ∈ s) :
    ‖f (lineMap x y c) - lineMap (f x) (f y) c‖ ≤
      C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by
  let z := lineMap x y c
  have hzx : z - x = c • (y - x) := by simp [z, lineMap_apply_module']
  have hdist : dist x z = ‖c‖ * dist x y := by
    rw [dist_eq_norm, show x - z = c • (x - y) by
      simp [z, lineMap_apply_module]; module, norm_smul, dist_eq_norm]
  have hbound : ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ ≤
      C * (‖c‖ ^ 2 * dist x y ^ 2) := by
    calc
      _ ≤ C * dist x z ^ 2 := h x hx z hz
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
      add_le_add hbound (mul_le_mul_of_nonneg_left (h x hx y hy) (norm_nonneg c))
    _ = C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by ring

private theorem eventually_add_smul_mem {s : Set E} (hs : s ∈ 𝓝 x) (v : E) :
    ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v ∈ s := by
  have htendsto : Tendsto (fun t : 𝕜 ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    have : ContinuousAt (fun t : 𝕜 ↦ x + t • v) 0 := by fun_prop
    simpa using this.tendsto
  exact htendsto hs

namespace HasQuadraticLineRemainderWithAt

/-- A quadratic line remainder bound in a neighborhood ensures that `lineDeriv` is the actual
line derivative at the center of the neighborhood. -/
theorem hasLineDerivAt (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v := by
  obtain ⟨s, hs, h⟩ := h
  have hx : x ∈ s := mem_of_mem_nhds hs
  have hmem : ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v ∈ s := eventually_add_smul_mem hs v
  change HasDerivAt (fun t : 𝕜 ↦ f (x + t • v)) (lineDeriv 𝕜 f x v) 0
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (IsBigO.of_bound (C * ‖v‖ ^ 2) ?_).trans_isLittleO
    (isLittleO_pow_id one_lt_two)
  filter_upwards [hmem] with t ht
  have ht_bound := h x hx (x + t • v) ht
  rw [show (x + t • v) - x = t • v by abel, lineDeriv_smul,
    dist_self_add_right, norm_smul, mul_pow] at ht_bound
  simpa only [zero_add, zero_smul, add_zero, norm_pow, mul_assoc, mul_left_comm, mul_comm]
    using ht_bound

/-- If the remainder from `lineDeriv` is uniformly bounded by a quadratic function in a
neighborhood of `x`, then the line derivative at `x` is linear in the direction. -/
theorem isLinearMap_lineDeriv (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
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
    (h.hasLineDerivAt q).sub
      (((h.hasLineDerivAt u').const_smul (1 - c)).add
        ((h.hasLineDerivAt v').const_smul c))
  have hg_zero : g 0 = 0 := by
    simp only [g, zero_smul, add_zero]
    module
  obtain ⟨s, hs, hbound⟩ := h
  have hu_mem : ∀ᶠ t : 𝕜 in 𝓝 0, x + t • u' ∈ s := eventually_add_smul_mem hs u'
  have hv_mem : ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v' ∈ s := eventually_add_smul_mem hs v'
  have hq_mem : ∀ᶠ t : 𝕜 in 𝓝 0, x + t • q ∈ s := eventually_add_smul_mem hs q
  have hg_bigO : g =O[𝓝 0] fun t : 𝕜 ↦ t ^ 2 := by
    refine IsBigO.of_bound (C * (‖c‖ ^ 2 + ‖c‖) * ‖v' - u'‖ ^ 2) ?_
    filter_upwards [hu_mem, hv_mem, hq_mem] with t hut hvt hqt
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
    refine (norm_image_lineMap_sub_lineMap_le_of_mem hbound hut hvt c ?_).trans_eq ?_
    · rwa [← hline]
    · rw [hdist, mul_pow, norm_pow]
      ring
  have hg_deriv_zero : HasDerivAt g 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa [hg_zero] using hg_bigO.trans_isLittleO (isLittleO_pow_id one_lt_two)
  exact sub_eq_zero.mp (hg_deriv.unique hg_deriv_zero)

/-- The line derivative at `x`, bundled as a linear map in its direction. -/
@[expose]
noncomputable def lineDerivLinearMap (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.isLinearMap_lineDeriv

@[simp]
theorem lineDerivLinearMap_apply (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (v : E) :
    h.lineDerivLinearMap v = lineDeriv 𝕜 f x v :=
  rfl

/-- A continuous linear line-derivative map is the Fréchet derivative. -/
theorem hasFDerivAt (h : HasQuadraticLineRemainderWithAt 𝕜 C f x)
    (hcont : Continuous h.lineDerivLinearMap) :
    HasFDerivAt f ⟨h.lineDerivLinearMap, hcont⟩ x := by
  obtain ⟨s, hs, hbound⟩ := h
  have hx : x ∈ s := mem_of_mem_nhds hs
  refine HasFDerivAt.of_isLittleO <| (IsBigO.of_bound C ?_).trans_isLittleO
    (isLittleO_pow_sub_sub x one_lt_two)
  filter_upwards [hs] with y hy
  simpa [dist_eq_norm, norm_sub_rev] using hbound x hx y hy

private theorem continuous_lineDerivLinearMap
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (hf : ContinuousAt f x) :
    Continuous h.lineDerivLinearMap := by
  classical
  let L := h.lineDerivLinearMap
  let r := fun v : E ↦ f (x + v) - f x - L v
  obtain ⟨s, hs, hbound⟩ := h
  have hx : x ∈ s := mem_of_mem_nhds hs
  have hadd : Tendsto (fun v : E ↦ x + v) (𝓝 0) (𝓝 x) := by
    have : ContinuousAt (fun v : E ↦ x + v) 0 := by fun_prop
    simpa using this.tendsto
  have hmem : ∀ᶠ v : E in 𝓝 0, x + v ∈ s := hadd hs
  let r' := fun v : E ↦ if x + v ∈ s then r v else 0
  have hr'_bound : ∀ v, ‖r' v‖ ≤ C * ‖v‖ ^ 2 := by
    intro v
    by_cases hv : x + v ∈ s
    · simpa [r', hv, r, L, dist_self_add_right] using hbound x hx (x + v) hv
    · simp only [r', hv, ↓reduceIte, norm_zero]
      positivity
  have hr' : Tendsto r' (𝓝 0) (𝓝 0) :=
    squeeze_zero_norm hr'_bound (by
      have : ContinuousAt (fun v : E ↦ C * ‖v‖ ^ 2) 0 := by fun_prop
      simpa using this.tendsto)
  have hr : Tendsto r (𝓝 0) (𝓝 0) :=
    hr'.congr' <| hmem.mono fun v hv ↦ by simp [r', hv]
  have hf_inc : Tendsto (fun v : E ↦ f (x + v) - f x) (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (fun _ : E ↦ f x) (𝓝 0) (𝓝 (f x)) := tendsto_const_nhds
    simpa using (hf.tendsto.comp hadd).sub hc
  apply continuous_of_tendsto_nhds_zero L
  have hlim := hf_inc.sub hr
  convert hlim using 1
  · funext v
    simp only [r]
    module
  · simp

/-- Under a uniform quadratic line remainder bound in a neighborhood of `x`, Fréchet
differentiability at `x` is equivalent to continuity at `x`. -/
theorem differentiableAt_iff_continuousAt
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    DifferentiableAt 𝕜 f x ↔ ContinuousAt f x :=
  ⟨DifferentiableAt.continuousAt, fun hf ↦
    (h.hasFDerivAt (continuous_lineDerivLinearMap h hf)).differentiableAt⟩

end HasQuadraticLineRemainderWithAt

namespace HasQuadraticLineRemainderWith

/-- A global quadratic line remainder bound holds in a neighborhood of every point. -/
theorem hasQuadraticLineRemainderWithAt
    (h : HasQuadraticLineRemainderWith 𝕜 C f) (x : E) :
    HasQuadraticLineRemainderWithAt 𝕜 C f x :=
  ⟨Set.univ, Filter.univ_mem, fun y _ z _ ↦ h y z⟩

/-- A uniform quadratic bound on the remainder from `lineDeriv` ensures that `lineDeriv` is the
actual line derivative. -/
theorem hasLineDerivAt (h : HasQuadraticLineRemainderWith 𝕜 C f) (x v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  (h.hasQuadraticLineRemainderWithAt x).hasLineDerivAt v

/-- A quadratic line remainder bound controls the failure of `f` to commute with affine
interpolation. -/
theorem norm_image_lineMap_sub_lineMap_le (h : HasQuadraticLineRemainderWith 𝕜 C f)
    (x y : E) (c : 𝕜) :
    ‖f (lineMap x y c) - lineMap (f x) (f y) c‖ ≤
      C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 :=
  norm_image_lineMap_sub_lineMap_le_of_mem (fun a _ b _ ↦ h a b)
    (Set.mem_univ x) (Set.mem_univ y) c (Set.mem_univ _)

/-- If the remainder from `lineDeriv` is uniformly bounded by a quadratic function, then the line
derivative is linear in the direction. -/
theorem isLinearMap_lineDeriv (h : HasQuadraticLineRemainderWith 𝕜 C f) (x : E) :
    IsLinearMap 𝕜 (lineDeriv 𝕜 f x) :=
  (h.hasQuadraticLineRemainderWithAt x).isLinearMap_lineDeriv

end HasQuadraticLineRemainderWith
