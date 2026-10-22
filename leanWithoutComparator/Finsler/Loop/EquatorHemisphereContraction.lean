module

public import Finsler.Loop.MeridianTransverseField
public import Finsler.Loop.NativeMatchingTestedPairing

/-! Contract the actual LOCAL equator hemisphere used by the same-leg
escape, preserving both the pole orthogonality and strict hemisphere
condition. Positive cohomology on this real patch therefore vanishes.
No global equator contraction is used. -/
@[expose] public section
namespace Finsler.EquatorHemisphereContraction
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.MeridianTransverseField Finsler.DiagonalGeometry
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def center {n : ℕ} (P : Sphere n) (v₀ : equator P) : space P v₀ :=
  ⟨v₀, by change 0 < ⟪(v₀.val : Ambient n), (v₀.val : Ambient n)⟫; rw [real_inner_self_eq_norm_sq, sphere_norm]; norm_num⟩

def blend {n : ℕ} (s : ClosedInterval) (P : Sphere n) (v₀ : equator P) (v : space P v₀) : Ambient n :=
  (1 - (s : ℝ)) • (v.val.val : Ambient n) + (s : ℝ) • (v₀.val : Ambient n)

theorem blend_positive {n : ℕ} (s : ClosedInterval) (P : Sphere n) (v₀ : equator P) (v : space P v₀) :
    0 < ⟪blend s P v₀ v, (v₀.val : Ambient n)⟫ := by
  rw [blend, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq, sphere_norm]
  have hv : 0 < ⟪(v.val.val : Ambient n), (v₀.val : Ambient n)⟫ := v.property
  by_cases h : (s : ℝ) = 1
  · rw [h]
    norm_num
  · have hs : 0 < 1 - (s : ℝ) := by
      by_contra hs
      apply h
      linarith [s.property.2]
    nlinarith [mul_pos hs hv, s.property.1]

theorem blend_ne_zero {n : ℕ} (s : ClosedInterval) (P : Sphere n) (v₀ : equator P) (v : space P v₀) :
    blend s P v₀ v ≠ 0 := by
  intro h
  have hp := blend_positive s P v₀ v
  rw [h, inner_zero_left] at hp
  exact lt_irrefl 0 hp

def deform {n : ℕ} (s : ClosedInterval) (P : Sphere n) (v₀ : equator P) (v : space P v₀) : space P v₀ := by
  let w := DiagonalGeometry.normalize (blend s P v₀ v) (blend_ne_zero s P v₀ v)
  have hwP : ⟪(P : Ambient n), (w : Ambient n)⟫ = 0 := by
    change ⟪(P : Ambient n), ‖blend s P v₀ v‖⁻¹ • blend s P v₀ v⟫ = 0
    rw [real_inner_smul_right, blend, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      v.val.property, v₀.property, mul_zero, mul_zero, add_zero, mul_zero]
  refine ⟨⟨w, hwP⟩, ?_⟩
  change 0 < ⟪(‖blend s P v₀ v‖⁻¹ • blend s P v₀ v : Ambient n), (v₀.val : Ambient n)⟫
  rw [real_inner_smul_left]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (blend_ne_zero s P v₀ v))) (blend_positive s P v₀ v)

theorem deform_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : space P v₀) : deform 0 P v₀ v = v := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ‖blend 0 P v₀ v‖⁻¹ • blend 0 P v₀ v = (v.val.val : Ambient n)
  simp only [blend, show ((0 : ClosedInterval) : ℝ) = 0 from rfl, sub_zero,
    one_smul, zero_smul, add_zero, sphere_norm, inv_one]

theorem deform_one {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : space P v₀) : deform 1 P v₀ v = center P v₀ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ‖blend 1 P v₀ v‖⁻¹ • blend 1 P v₀ v = (v₀.val : Ambient n)
  simp only [blend, show ((1 : ClosedInterval) : ℝ) = 1 from rfl, sub_self,
    zero_smul, one_smul, zero_add, sphere_norm, inv_one]

theorem deform_continuous {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Continuous (fun z : ClosedInterval × space P v₀ => deform z.1 P v₀ z.2) := by
  have hs : Continuous (fun z : ClosedInterval × space P v₀ => (z.1 : ℝ)) := by fun_prop
  have hv : Continuous (fun z : ClosedInterval × space P v₀ => (z.2.val.val : Ambient n)) := by fun_prop
  have hb : Continuous (fun z : ClosedInterval × space P v₀ => blend z.1 P v₀ z.2) :=
    ((continuous_const.sub hs).smul hv).add (hs.smul continuous_const)
  have hi := hb.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (blend_ne_zero z.1 P v₀ z.2))
  exact (((hi.smul hb).subtype_mk _).subtype_mk _).subtype_mk _

def contraction {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (𝟙 (space P v₀)) (TopCat.ofHom (ContinuousMap.const (space P v₀) (center P v₀))) where
  toFun z := deform z.1 P v₀ z.2
  continuous_toFun := deform_continuous P v₀
  map_zero_left := deform_zero P v₀
  map_one_left := deform_one P v₀

theorem positive_cohomology_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (space P v₀) q) : a = 0 := by
  have he := LoopSweepTwoPiece.cohomology_homotopy (contraction P v₀) q a
  rw [Finsler.DiagonalCohomology.pullback_id] at he
  exact he.trans (NativeMatchingTestedPairing.constant_pullback_zero (space P v₀) (space P v₀) (center P v₀) q hq a)

end
end Finsler.EquatorHemisphereContraction
