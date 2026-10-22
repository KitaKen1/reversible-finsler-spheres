module

public import Finsler.Geometry.MetricComparison
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! An actual nearby orthogonal map, given by two axis reflections.
It carries x to y for equal-length vectors, is the identity on the diagonal,
and varies continuously near a nonzero diagonal point. -/

@[expose] public section

namespace Finsler.NearbyRotor

open Finsler.SphereGeometry
open scoped Topology RealInnerProductSpace

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def axisReflection (u : Ambient n) : Ambient n ≃ₗᵢ[ℝ] Ambient n :=
  Submodule.reflection (ℝ ∙ u)

theorem axis_formula (u : Ambient n) :
    (axisReflection u).toContinuousLinearMap =
      (2 / ‖u‖ ^ 2) • (innerSL ℝ u).smulRight u -
        ContinuousLinearMap.id ℝ (Ambient n) := by
  apply ContinuousLinearMap.ext
  intro v
  change Submodule.reflection (ℝ ∙ u) v =
    (2 / ‖u‖ ^ 2) • (⟪u, v⟫ • u) - v
  rw [Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hc : 2 • (⟪u, v⟫ / ‖u‖ ^ 2) = (2 / ‖u‖ ^ 2) * ⟪u, v⟫ := by
    simp only [two_smul]
    ring
  have he := congrArg (fun r : ℝ => r • u - v) hc
  simpa only [two_smul, add_smul, mul_smul] using he

theorem axis_continuousAt {u : Ambient n} (hu : u ≠ 0) :
    ContinuousAt (fun v : Ambient n => (axisReflection v).toContinuousLinearMap) u := by
  have hT : Continuous (fun v : Ambient n => (innerSL ℝ v).smulRight v) :=
    ((ContinuousLinearMap.smulRightL ℝ (Ambient n) (Ambient n)).continuous.comp
      (innerSL ℝ).continuous).clm_apply continuous_id
  have hscalar : ContinuousAt (fun v : Ambient n => (2 : ℝ) / ‖v‖ ^ 2) u :=
    continuousAt_const.div (continuousAt_id.norm.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))
  have he := (hscalar.smul hT.continuousAt).sub
    (show ContinuousAt (fun _ : Ambient n => ContinuousLinearMap.id ℝ (Ambient n)) u
      from continuousAt_const)
  exact he.congr (Filter.Eventually.of_forall fun v => (axis_formula v).symm)

theorem axis_sum_map {x y : Ambient n} (h : ‖x‖ = ‖y‖) :
    axisReflection (x + y) x = y := by
  have he := Submodule.reflection_sub (v := x) (w := -y) (by simpa using h)
  rw [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at he
  exact neg_injective he

def rotor (x y : Ambient n) : Ambient n ≃ₗᵢ[ℝ] Ambient n :=
  (axisReflection x).trans (axisReflection (x + y))

theorem rotor_map {x y : Ambient n} (h : ‖x‖ = ‖y‖) : rotor x y x = y := by
  change axisReflection (x + y) (Submodule.reflection (ℝ ∙ x) x) = y
  rw [Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self x)]
  exact axis_sum_map h

theorem rotor_self (x : Ambient n) : rotor x x = LinearIsometryEquiv.refl ℝ (Ambient n) := by
  have hs : (ℝ ∙ (x + x)) = ℝ ∙ x := by
    rw [← two_smul ℝ x]
    exact Submodule.span_singleton_smul_eq
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0)) x
  unfold rotor axisReflection
  simpa only [hs] using Submodule.reflection_trans_reflection (ℝ ∙ x)

theorem rotor_continuousAt {x y : Ambient n} (hx : x ≠ 0) (hxy : x + y ≠ 0) :
    ContinuousAt (fun p : Ambient n × Ambient n => (rotor p.1 p.2).toContinuousLinearMap)
      (x, y) := by
  have h1 := (axis_continuousAt hx).comp
    (f := fun p : Ambient n × Ambient n => p.1) (x := (x, y)) continuousAt_fst
  have hs : ContinuousAt (fun p : Ambient n × Ambient n => p.1 + p.2) (x, y) := by
    exact ((continuousAt_fst (p := (x, y))).add continuousAt_snd).congr
      (Filter.Eventually.of_forall fun p => rfl)
  have h2 := (axis_continuousAt hxy).comp
    (f := fun p : Ambient n × Ambient n => p.1 + p.2) (x := (x, y)) hs
  have he (p : Ambient n × Ambient n) : (rotor p.1 p.2).toContinuousLinearMap =
      (axisReflection (p.1 + p.2)).toContinuousLinearMap.comp
        (axisReflection p.1).toContinuousLinearMap := by
    ext v
    rfl
  simpa only [he, Function.comp_apply] using h2.clm_comp h1

theorem exists_close_rotor {x : Ambient n} (hx : x ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : Ambient n, dist y x < ρ →
      ‖(rotor x y).toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ := by
  have hsum : x + x ≠ 0 := by
    rw [← two_smul ℝ x]
    exact smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hx
  have hc := (rotor_continuousAt hx hsum).comp
    (continuousAt_const.prodMk (continuousAt_id (x := x)))
  obtain ⟨ρ, hρ, hd⟩ := Metric.continuousAt_iff.mp hc δ hδ
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have hid : (rotor x x).toContinuousLinearMap = ContinuousLinearMap.id ℝ (Ambient n) := by
    rw [rotor_self]
    ext v
    rfl
  have he := hd hy
  simpa only [Function.comp_apply, hid, dist_eq_norm] using he


end
end Finsler.NearbyRotor
