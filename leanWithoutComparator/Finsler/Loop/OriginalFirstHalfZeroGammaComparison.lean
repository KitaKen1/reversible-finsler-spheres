module

public import Finsler.Loop.OriginalFirstHalfZeroGammaCap
public import Finsler.Loop.FirstInputRotationAmbientGammaCap
public import Finsler.Topology.SmallRetractionComparison

/-! Exact small-chain comparison of the real zero-cylinder gamma
cap with the established bounded two-stage rotating cap. This is a
source equality before the time prism, not a cycle-only shortcut. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroGammaComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfZeroCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η ρ : ℝ)

def smallAmbientMap : small (space α β R) (cover α β R r η ρ) ⟶
    small (FirstInputRotationAmbientCover.ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ) :=
  SmallRetractionComparison.map (cover α β R r η ρ) (FirstInputRotationAmbientCover.cover α β R r η ρ)
    (OriginalFirstHalfCupOneCochains.rotatingZero α β R) id (fun _ _ hz => hz)

theorem smallAmbientMap_inclusion : smallAmbientMap α β R r η ρ ≫
    inclusion (FirstInputRotationAmbientCover.ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ) =
    inclusion (space α β R) (cover α β R r η ρ) ≫ push (OriginalFirstHalfCupOneCochains.rotatingZero α β R) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

variable (hR : R ≤ 1 / 2) (hr : r < 1) {δ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B : ℝ)

theorem source_original : OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B ≫
    OriginalFirstHalfCupOneCochains.nearSource α β R = OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (oldGood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem component_compare (q : ℕ) :
    OriginalFirstHalfZeroGammaCap.component α β R r hR hr h p T F B η good q ≫
      (push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B)).f q =
    (smallAmbientMap α β R r η ρ).f (((m + 1) + p) + q) ≫
      (FirstInputRotationAmbientCap.operation α β R r hR hr p T (by omega) h F B η oldGood hT).component q := by
  let c := OriginalFirstHalfZeroGammaCap.component α β R r hR hr h p T F B η good q
  let a := (FirstInputRotationAmbientCap.operation α β R r hR hr p T (by omega) h F B η oldGood hT).component q
  let j := push (FirstInputRotationAmbientCap.source α β R r hR hr F B)
  let s := push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B)
  let f := push (OriginalFirstHalfCupOneCochains.rotatingZero α β R)
  haveI := FirstInputRotationAmbientCap.source_mono α β R r hR hr F B q
  apply (cancel_mono (j.f q)).mp
  change (c ≫ s.f q) ≫ j.f q = ((smallAmbientMap α β R r η ρ).f (((m + 1) + p) + q) ≫ a) ≫ j.f q
  have hs := congrArg (fun g => (push g).f q)
    (OriginalFirstHalfZeroSupportedCap.sourceBounded_stage α β R r hR hr F B)
  simp only [push_comp, HomologicalComplex.comp_f] at hs
  have hc := OriginalFirstHalfZeroGammaCap.component_source α β R r hR hr h p T F B η good q
  have ha := FirstInputRotationAmbientGammaCap.component_source α β R r hR hr p T h F B η oldGood hT q
  have hi := congrArg (fun g => g.f (((m + 1) + p) + q)) (smallAmbientMap_inclusion α β R r η ρ)
  simp only [HomologicalComplex.comp_f] at hi
  have hn := RelativeCapBoundary.absolute_chain_natural (OriginalFirstHalfCupOneCochains.rotatingZero α β R)
    ((m + 1) + p) q (((m + 1) + p) + q) rfl (FirstInputRotationAmbientCupOne.gamma α β R r hR hr h p T)
  rw [← OriginalFirstHalfZeroGammaCochains.ambient_restriction α β R r hR hr h p T] at hn
  change absoluteChain (space α β R) ((m + 1) + p) q (((m + 1) + p) + q) rfl
      (OriginalFirstHalfZeroGammaCochains.gamma α β R r hr h p T) ≫ f.f q =
    f.f (((m + 1) + p) + q) ≫ absoluteChain (FirstInputRotationAmbientCover.ambient α β R)
      ((m + 1) + p) q (((m + 1) + p) + q) rfl (FirstInputRotationAmbientCupOne.gamma α β R r hR hr h p T) at hn
  calc
    _ = (c ≫ (push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B)).f q) ≫ f.f q := by
      simp only [Category.assoc]
      rw [hs]
    _ = ((inclusion (space α β R) (cover α β R r η ρ)).f (((m + 1) + p) + q) ≫
        absoluteChain (space α β R) ((m + 1) + p) q (((m + 1) + p) + q) rfl
          (OriginalFirstHalfZeroGammaCochains.gamma α β R r hr h p T)) ≫ f.f q := by rw [hc]
    _ = ((inclusion (space α β R) (cover α β R r η ρ)).f (((m + 1) + p) + q) ≫ f.f (((m + 1) + p) + q)) ≫
        absoluteChain (FirstInputRotationAmbientCover.ambient α β R) ((m + 1) + p) q (((m + 1) + p) + q) rfl
          (FirstInputRotationAmbientCupOne.gamma α β R r hR hr h p T) := by rw [Category.assoc, hn, ← Category.assoc]
    _ = ((smallAmbientMap α β R r η ρ).f (((m + 1) + p) + q) ≫
        (inclusion (FirstInputRotationAmbientCover.ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ)).f
          (((m + 1) + p) + q)) ≫ absoluteChain (FirstInputRotationAmbientCover.ambient α β R)
          ((m + 1) + p) q (((m + 1) + p) + q) rfl (FirstInputRotationAmbientCupOne.gamma α β R r hR hr h p T) := by rw [hi]
    _ = _ := by
      simp only [Category.assoc]
      rw [ha]

theorem homology_compare (q : ℕ) :
    ((OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η good hT).post
      (push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B))).homology q =
    ((FirstInputRotationAmbientCap.operation α β R r hR hr p T (by omega) h F B η oldGood hT).pre
      (smallAmbientMap α β R r η ρ)).homology q := by
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro i
  exact component_compare α β R r η ρ hR hr h p T F B good oldGood hT i

theorem retained_component_compare (q : ℕ) :
    OriginalFirstHalfZeroGammaCap.component α β R r hR hr h p T F B η good q ≫
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B)).f q =
    (smallAmbientMap α β R r η ρ).f (((m + 1) + p) + q) ≫
      (FirstInputRotationAmbientCap.retainedOperation α β R r hR hr p T (by omega) h F B η oldGood hT).component q := by
  have hc := congrArg (fun g => g ≫ (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B)).f q)
    (component_compare α β R r η ρ hR hr h p T F B good oldGood hT q)
  simpa only [OriginalFirstHalfJointSupportedCap.retained, push_comp, HomologicalComplex.comp_f,
    FirstInputRotationAmbientCap.retainedOperation, DegreeLoweringHomology.Map.post, Category.assoc] using hc

end
end Finsler.OriginalFirstHalfZeroGammaComparison
