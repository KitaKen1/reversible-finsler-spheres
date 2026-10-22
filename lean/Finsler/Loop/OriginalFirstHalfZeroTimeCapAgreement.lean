module

public import Finsler.Loop.OriginalFirstHalfZeroGammaTime
public import Finsler.Loop.FirstInputRotationTimeEndpoints
public import Finsler.Loop.CylinderCommonCover

/-! Exact actual source and common-cover diagrams comparing the
original zero-cylinder gamma cap with the existing rotation-zero
cut-time-first two-cap model, before applying the time prism. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroTimeCapAgreement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem thom_restriction :
    cochainPullback (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0) (m + 1)
      (FirstInputRotationCutCylinder.thom α β R hR (by omega) h) =
    OriginalFirstHalfZeroGammaTime.thom α β R h := by
  rw [FirstInputRotationCutCylinder.thom, ← pullback_comp]
  exact (OriginalFirstHalfGammaCaps.near_thom α β h R hR).symm

theorem tested_restriction :
    cochainPullback (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0) p
      (FirstInputRotationCutCylinder.tested α β R r hR hr p T) =
    OriginalFirstHalfZeroGammaTime.tested α β R r hr p T := by
  rw [FirstInputRotationCutCylinder.tested, ← pullback_comp]
  exact (OriginalFirstHalfGammaCaps.near_tested α β r hr p T R hR).symm

variable (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (oldGood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem source_time :
    OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B ≫
      FirstInputRotationTimeCap.source α β R r hR hr F B =
    OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B ≫
      FirstInputRotationTimeEndpoints.cylinderSlice α β R 0 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem component_agreement (q : ℕ) :
    (CylinderCommonCover.toSource (OriginalFirstHalfZeroCover.cover α β R r η ρ)
      (FirstInputRotationCutCylinder.cover α β R r η ρ) (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0)).f
      ((m + 1) + (p + q)) ≫
      OriginalFirstHalfZeroGammaTime.component α β R r hR hr h p T F B η goodΓ hT q ≫
        (push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B)).f q =
    (CylinderCommonCover.toTarget (OriginalFirstHalfZeroCover.cover α β R r η ρ)
      (FirstInputRotationCutCylinder.cover α β R r η ρ) (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0)).f
      ((m + 1) + (p + q)) ≫
      FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η oldGood hT q := by
  let Y := OriginalFirstHalfZeroCover.space α β R
  let Z := FirstInputRotationCutCylinder.cylinder α β R
  let U := OriginalFirstHalfZeroCover.cover α β R r η ρ
  let V := FirstInputRotationCutCylinder.cover α β R r η ρ
  let f := FirstInputRotationTimeEndpoints.cylinderSlice α β R 0
  let Ms := CylinderCommonCover.toSource U V f
  let Mt := CylinderCommonCover.toTarget U V f
  let c := OriginalFirstHalfZeroGammaTime.component α β R r hR hr h p T F B η goodΓ hT q
  let d := FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η oldGood hT q
  let s := push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B)
  let b := push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B)
  let j := push (FirstInputRotationTimeCap.source α β R r hR hr F B)
  haveI := FirstInputRotationTimeCap.source_mono α β R r hR hr F B q
  apply (cancel_mono (j.f q)).mp
  change (Ms.f ((m + 1) + (p + q)) ≫ c ≫ s.f q) ≫ j.f q =
    (Mt.f ((m + 1) + (p + q)) ≫ d) ≫ j.f q
  have hs := congrArg (fun g => (push g).f q) (source_time α β R r hR hr F B)
  simp only [push_comp, HomologicalComplex.comp_f] at hs
  have hi : Mt ≫ inclusion Z V = Ms ≫ inclusion Y U ≫ push f := by
    rw [CylinderCommonCover.toTarget_inclusion, ← Category.assoc, CylinderCommonCover.toSource_inclusion]
  have hiq := congrArg (fun g => g.f ((m + 1) + (p + q))) hi
  simp only [HomologicalComplex.comp_f] at hiq
  have hn := PartialDoubleCap.cap_natural f (m + 1) p q
    (FirstInputRotationCutCylinder.thom α β R hR (by omega) h)
    (FirstInputRotationCutCylinder.tested α β R r hR hr p T)
  rw [thom_restriction α β R hR h, tested_restriction α β R r hR hr p T] at hn
  calc
    _ = Ms.f ((m + 1) + (p + q)) ≫ (c ≫ b.f q) ≫ (push f).f q := by
      simp only [Category.assoc]
      rw [hs]
    _ = Ms.f ((m + 1) + (p + q)) ≫ (inclusion Y U).f ((m + 1) + (p + q)) ≫
        PartialDoubleCap.cap Y (m + 1) p q (OriginalFirstHalfZeroGammaTime.thom α β R h)
          (OriginalFirstHalfZeroGammaTime.tested α β R r hr p T) ≫ (push f).f q := by
      rw [OriginalFirstHalfZeroGammaTime.component_source]
      simp only [Y, U, Category.assoc]
    _ = (Mt.f ((m + 1) + (p + q)) ≫ (inclusion Z V).f ((m + 1) + (p + q))) ≫
        PartialDoubleCap.cap Z (m + 1) p q (FirstInputRotationCutCylinder.thom α β R hR (by omega) h)
          (FirstInputRotationCutCylinder.tested α β R r hR hr p T) := by
      simp only [Category.assoc]
      rw [hn]
      simpa only [Category.assoc] using congrArg (fun k => k ≫
        PartialDoubleCap.cap Z (m + 1) p q (FirstInputRotationCutCylinder.thom α β R hR (by omega) h)
          (FirstInputRotationCutCylinder.tested α β R r hR hr p T)) hiq.symm
    _ = _ := by
      simpa only [d, Z, V, j, Category.assoc] using
        congrArg (fun k => Mt.f ((m + 1) + (p + q)) ≫ k)
          (FirstInputRotationTimeCap.component_source α β R r hR hr p T (by omega) h F B η oldGood hT q).symm

end
end Finsler.OriginalFirstHalfZeroTimeCapAgreement
