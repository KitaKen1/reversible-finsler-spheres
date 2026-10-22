module

public import Finsler.Loop.OriginalFirstHalfZeroTimeCapAgreement
public import Finsler.Loop.CutTimeCommonComparison
public import Finsler.Loop.FirstInputRotationJoinedTime
public import Finsler.Loop.DegreeLoweringCompositionPostHomology

/-! Genuine relative comparison of original gamma time with the
established rotation-zero time operation, before and after retaining.
The actual first spatial cap may then be composed on ordinary input. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroTimeComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B η : ℝ) (hη : 0 < η) (hρr : ρ < r)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (oldGood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def oldEndpoint := (FirstInputRotationFullTime.operation α β R r hR hr p T h F B η hη hρr oldGood hT).pre
  (push (FirstInputRotationTimeEndpoints.slice α β R 0))

theorem old_component_normal (q : ℕ) :
    (oldEndpoint α β R r hR hr h p T F B η hη hρr oldGood hT).component q =
    AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
      (push (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0) ≫
        TauCeti.smallSingularRetraction (X := FirstInputRotationCutCylinder.cylinder α β R) coeff
          (FirstInputRotationCutCylinder.cover α β R r η ρ)
          (FirstInputRotationCutCylinder.cover_open α β R r η ρ)
          (FirstInputRotationCutCylinder.cover_univ α β R r η hη hρr)).f ((m + p) + q + 1) ≫
      ClosedCapDegreeTransport.align m p
        (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η oldGood hT) q := by
  dsimp only [oldEndpoint, DegreeLoweringHomology.Map.pre]
  rw [FirstInputRotationFullTime.component_normal, ← Category.assoc, FirstInputRotationTimeEndpoints.slice_prism]
  let Rt := TauCeti.smallSingularRetraction (X := FirstInputRotationCutCylinder.cylinder α β R) coeff
    (FirstInputRotationCutCylinder.cover α β R r η ρ)
    (FirstInputRotationCutCylinder.cover_open α β R r η ρ)
    (FirstInputRotationCutCylinder.cover_univ α β R r η hη hρr)
  have he : FirstInputRotationFullTime.retracted α β R r hR hr p T h F B η hη hρr oldGood hT =
      (fun t => Rt.f ((m + 1) + (p + t)) ≫
        FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η oldGood hT t) := rfl
  rw [he, ClosedCapFunctoriality.align_pre]
  simp only [Rt, HomologicalComplex.comp_f, Category.assoc]

theorem time_homology_eq (q : ℕ) :
    ((OriginalFirstHalfZeroGammaTime.operation α β R r hR hr h p T F B η hη hρr goodΓ hT).post
      (push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B))).homology q =
    (oldEndpoint α β R r hR hr h p T F B η hη hρr oldGood hT).homology q := by
  apply CutTimeCommonComparison.homology_eq
    (TopCat.of (CompactNearJoinParameters.tube α β R)) (FirstInputRotationCutCylinder.cylinder α β R)
    (OriginalFirstHalfZeroCover.cover α β R r η ρ) (FirstInputRotationCutCylinder.cover α β R r η ρ)
    (OriginalFirstHalfZeroCover.cover_open α β R r η ρ) (OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr)
    (FirstInputRotationCutCylinder.cover_open α β R r η ρ) (FirstInputRotationCutCylinder.cover_univ α β R r η hη hρr)
    (FirstInputRotationTimeEndpoints.cylinderSlice α β R 0)
    _ _ (push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B)) m p
    (OriginalFirstHalfZeroGammaTime.component α β R r hR hr h p T F B η goodΓ hT)
    (OriginalFirstHalfZeroGammaTime.component_comm α β R r hR hr h p T F B η goodΓ hT)
    (OriginalFirstHalfZeroGammaTime.inner α β R (δ := δ)) (OriginalFirstHalfZeroGammaTime.thom α β R h)
    (OriginalFirstHalfZeroGammaTime.tested α β R r hr p T) (OriginalFirstHalfZeroGammaTime.thom_inner_zero α β R h)
    (push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B))
    (OriginalFirstHalfZeroSupportedCap.sourceBounded_mono α β R r hR hr F B)
    (OriginalFirstHalfZeroGammaTime.component_source α β R r hR hr h p T F B η goodΓ hT)
    (fun z => show distance (m + 1) (0, α z.val.1) ≤ δ from (UniformSelfCutCollar.distance_zero α z.val.1).le.trans h.1.le)
    (fun z => show distance (m + 1) (1, α z.val.1) ≤ δ from (UniformSelfCutCollar.distance_one α z.val.1).le.trans h.1.le)
    (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η oldGood hT)
    (FirstInputRotationTimeCap.component_comm α β R r hR hr p T (by omega) h F B η oldGood hT)
    (OriginalFirstHalfZeroTimeCapAgreement.component_agreement α β R r hR hr h p T F B η goodΓ oldGood hT)
    (OriginalFirstHalfZeroGammaTime.operation α β R r hR hr h p T F B η hη hρr goodΓ hT)
    (OriginalFirstHalfZeroGammaTime.component_normal α β R r hR hr h p T F B η hη hρr goodΓ hT)
    (oldEndpoint α β R r hR hr h p T F B η hη hρr oldGood hT)
    (old_component_normal α β R r hR hr h p T F B η hη hρr oldGood hT) q

theorem retained_time_homology_eq (q : ℕ) :
    ((OriginalFirstHalfZeroGammaTime.operation α β R r hR hr h p T F B η hη hρr goodΓ hT).post
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B))).homology q =
    (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F B η hη hρr oldGood hT 0).homology q := by
  have he := congrArg (fun k => k ≫ HomologicalComplex.homologyMap
    (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B)) q)
    (time_homology_eq α β R r hR hr h p T F B η hη hρr goodΓ oldGood hT q)
  simpa only [OriginalFirstHalfJointSupportedCap.retained, push_comp, HomologicalComplex.homologyMap_comp,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.pre_homology,
    oldEndpoint, FirstInputRotationTimeEndpoints.endpoint, FirstInputRotationFullTime.retainedOperation,
    Category.assoc] using he

def joined {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) :=
  (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR)
    (OriginalFirstHalfZeroGammaTime.operation α β R r hR hr h p T F B η hη hρr goodΓ hT)).post
    (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B))

theorem joined_existing {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (q : ℕ) :
    (joined α β R r hR hr h p T F B η hη hρr goodΓ hT hκ hκR).homology q =
    (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F B η hη hρr oldGood hT 0).homology q :=
  DegreeLoweringCompositionPostHomology.post_congr _ _ _ _ q
    (retained_time_homology_eq α β R r hR hr h p T F B η hη hρr goodΓ oldGood hT q)

end
end Finsler.OriginalFirstHalfZeroTimeComparison
