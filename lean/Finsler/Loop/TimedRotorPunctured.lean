module

public import Finsler.Loop.H1PuncturedEvaluationChart
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The existing rotor path is continuous on the WHOLE punctured
sphere, including its inverse operator. At time zero it is identity;
at time one it sends the chosen endpoint to the chart pole. -/
@[expose] public section
namespace Finsler.TimedRotorPunctured
open CategoryTheory Topology
open Finsler.SphereGeometry Finsler.NearbyRotor Finsler.RotorHomotopy
open Finsler.H1PuncturedEvaluationChart
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000
local notation "I" => _root_.unitInterval

theorem axis_ne_zero {n : ℕ} (a x : Sphere n) (hx : x ∈ base a) (s : I) :
    (x : Ambient n) + blend s (x : Ambient n) (a : Ambient n) ≠ 0 := by
  intro h
  have he : (2 - (s : ℝ)) • (x : Ambient n) = -((s : ℝ) • (a : Ambient n)) := by
    apply eq_neg_of_add_eq_zero_left
    calc (2 - (s : ℝ)) • (x : Ambient n) + (s : ℝ) • (a : Ambient n) =
        (x : Ambient n) + blend s (x : Ambient n) (a : Ambient n) := by
          simp only [blend, sub_smul, two_smul, one_smul]
          abel
      _ = 0 := h
  have hxnorm : ‖(x : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hanorm : ‖(a : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp a.property
  have hpos : 0 ≤ 2 - (s : ℝ) := by linarith [s.property.2]
  have hn : 2 - (s : ℝ) = (s : ℝ) := by
    simpa only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos,
      abs_of_nonneg s.property.1, hxnorm, hanorm, mul_one] using congrArg norm he
  have hsval : (s : ℝ) = 1 := by linarith
  have hs : s = (1 : I) := Subtype.ext hsval
  apply sum_ne_zero x a hx
  simpa only [hs, blend, show ((1 : I) : ℝ) = 1 from rfl,
    sub_self, zero_smul, one_smul, zero_add] using h

theorem operator_continuous {n : ℕ} (a : Sphere n) :
    Continuous (fun p : I × base a => (path p.1 (p.2.val : Ambient n) (a : Ambient n)).toContinuousLinearMap) := by
  have ht : Continuous (fun p : I × base a => (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : I × base a => (p.2.val : Ambient n)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hb : Continuous (fun p : I × base a => blend p.1 (p.2.val : Ambient n) (a : Ambient n)) :=
    ((continuous_const.sub ht).smul hx).add (ht.smul continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hn : (p.2.val : Ambient n) ≠ 0 := by
    have hnorm : ‖(p.2.val : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.val.property
    exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  exact (rotor_continuousAt hn (axis_ne_zero a p.2.val p.2.property p.1)).comp
    (f := fun q : I × base a => ((q.2.val : Ambient n), blend q.1 (q.2.val : Ambient n) (a : Ambient n)))
    (hx.prodMk hb).continuousAt

theorem inverse_operator_continuous {n : ℕ} (a : Sphere n) :
    Continuous (fun p : I × base a => (path p.1 (p.2.val : Ambient n) (a : Ambient n)).symm.toContinuousLinearMap) := by
  have hc : Continuous (fun p : I × base a =>
      ContinuousLinearMap.adjoint (path p.1 (p.2.val : Ambient n) (a : Ambient n)).toContinuousLinearMap) :=
    ContinuousLinearMap.adjoint.continuous.comp (operator_continuous a)
  exact hc.congr (fun p => (path p.1 (p.2.val : Ambient n) (a : Ambient n)).adjoint_eq_symm)

def sphereMap {n : ℕ} (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (x : Sphere n) : Sphere n :=
  ⟨A (x : Ambient n), mem_sphere_zero_iff_norm.mpr
    ((A.norm_map _).trans (mem_sphere_zero_iff_norm.mp x.property))⟩

theorem sphereMap_symm_apply {n : ℕ} (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (x : Sphere n) :
    sphereMap A.symm (sphereMap A x) = x := Subtype.ext (A.symm_apply_apply _)

theorem sphereMap_apply_symm {n : ℕ} (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (x : Sphere n) :
    sphereMap A (sphereMap A.symm x) = x := Subtype.ext (A.apply_symm_apply _)

end
end Finsler.TimedRotorPunctured
