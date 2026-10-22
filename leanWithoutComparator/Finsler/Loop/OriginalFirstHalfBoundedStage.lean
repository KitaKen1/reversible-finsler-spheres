module

public import Finsler.Loop.OriginalFirstHalfJointSupportedCap
public import Finsler.Loop.FirstInputRotationTimeCap

/-! Actual source and retained squares from the bounded zero slice
to the established bounded rotating cut model. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfBoundedStage

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfJointSupportedCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric (m + 1)) (B : ℝ)

theorem source_proper :
    boundedStage α β R r hR hr F B ≫ FirstInputRotationFilteredCap.source α β R r hR hr F B =
    SupportedCap.subspaceMap (TopCat.of (FirstInputRotatingCut.source α β R r)) (bounded α β R r hR hr F B) ≫
      FirstInputRotationEndpoints.stage α β R r 0 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem source_ambient :
    boundedStage α β R r hR hr F B ≫ FirstInputRotationAmbientCap.source α β R r hR hr F B =
    SupportedCap.subspaceMap (TopCat.of (FirstInputRotatingCut.source α β R r)) (bounded α β R r hR hr F B) ≫
      FirstInputRotationEndpoints.stage α β R r 0 ≫ FirstInputRotationAmbientCover.source α β R r := by
  rw [FirstInputRotationAmbientCap.source, ← Category.assoc, source_proper, Category.assoc]

theorem source_time :
    boundedStage α β R r hR hr F B ≫ FirstInputRotationTimeCap.source α β R r hR hr F B =
    SupportedCap.subspaceMap (TopCat.of (FirstInputRotatingCut.source α β R r)) (bounded α β R r hR hr F B) ≫
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (FirstInputRotatingCut.source α β R r) ≫ FirstInputRotationTimeEndpoints.cylinderSlice α β R 0 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem source_original : source α β R r hR hr F B =
    SupportedCap.subspaceMap (TopCat.of (FirstInputRotatingCut.source α β R r)) (bounded α β R r hR hr F B) ≫
      OriginalFirstHalfJointCover.source α β R r := rfl

theorem source_original_near : source α β R r hR hr F B =
    SupportedCap.subspaceMap (TopCat.of (FirstInputRotatingCut.source α β R r)) (bounded α β R r hR hr F B) ≫
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (FirstInputRotatingCut.source α β R r) ≫ OriginalFirstHalfCupOneCochains.nearSource α β R := by
  rw [source_original, OriginalFirstHalfJointCover.source_near]

theorem retained_square : retained α β R r hR hr F B =
    boundedStage α β R r hR hr F B ≫ FirstInputRotationFilteredCap.retained α β R r hR hr F B := rfl

theorem boundedStage_mono (q : ℕ) : Mono ((push (boundedStage α β R r hR hr F B)).f q) := by
  haveI : Mono (boundedStage α β R r hR hr F B) := by
    apply (TopCat.mono_iff_injective _).mpr
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : FirstInputRotationFilteredCap.domain α β R r hR hr F B => z.val.2) h
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (boundedStage α β R r hR hr F B)).app (Opposite.op ⦋q⦌))))

end
end Finsler.OriginalFirstHalfBoundedStage
