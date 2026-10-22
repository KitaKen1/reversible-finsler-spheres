module

public import Finsler.Loop.NativeOrderedSegmentValues

/-! Exact remaining obstruction for the OLD GLOBAL coefficient:
coefficient = ONE + the actual six partial same-leg contributions.
All SIX chronological distinct-leg terms are now evaluated on the
original input. No vanishing of the same-leg sum is assumed. -/
@[expose] public section
namespace Finsler.NativeOriginalCoefficientResidual
open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativeMovingGlobalDecomposition Finsler.NativeOrderedSegmentValues
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem original_coefficient_residual (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ = 1 + sameLegScalar m hm P v₀ hρ hρr hr hη := by
  rw [NativeOrderedZeroClasses.coefficient_nine m hm P v₀ hρ hρr hr hη hr8 hη8]
  simp_rw [last_target_segments_one m hm P v₀ _ hρ hρr hr hη hr8 hη8]
  unfold sameLegScalar
  simp only [Fin.sum_univ_three]
  ring_nf
  norm_num
  decide

theorem original_distinct_sum_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    distinctLegScalar m hm P v₀ hρ hρr hr hη = 1 :=
  add_right_cancel ((original_coefficient_eighth m hm P v₀ hρ hρr hr hη hr8 hη8).symm.trans
    (original_coefficient_residual m hm P v₀ hρ hρr hr hη hr8 hη8))

theorem coefficient_one_iff_sameLeg_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ = 1 ↔ sameLegScalar m hm P v₀ hρ hρr hr hη = 0 := by
  rw [original_coefficient_residual m hm P v₀ hρ hρr hr hη hr8 hη8]
  constructor
  · intro h
    exact add_left_cancel (h.trans (add_zero (1 : ZMod 2)).symm)
  · intro h
    rw [h, add_zero]

end
end Finsler.NativeOriginalCoefficientResidual
