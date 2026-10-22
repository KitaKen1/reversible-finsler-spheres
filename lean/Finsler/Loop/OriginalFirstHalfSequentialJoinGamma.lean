module

public import Finsler.Loop.OriginalFirstHalfLocalizedJoinCap
public import Finsler.Loop.OriginalFirstHalfZeroGammaComparison
public import Finsler.Loop.LocalizedCapCupRegradedSource

/-! The genuine localized spatial join followed by the actual gamma
cap, with literal source and existing bounded two-cap comparison. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfSequentialJoinGamma

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def operation : DegreeLoweringHomology.Map
    (small (ambient α β) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ))
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B)))
    (((m + 1) + (m + p)) + 1) :=
  DegreeLoweringRegrade.regrade
    (DegreeLoweringComposition.compose (OriginalFirstHalfLocalizedJoinCap.operation α β R r η ρ hκ)
      (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η good hT))
    (((m + 1) + (m + p)) + 1) (by omega)

theorem component_source (q : ℕ) :
    (operation α β R r η hR hr h p T hκ F B good hT).component q ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ)).f
      ((((m + 1) + (m + p)) + 1) + q) ≫
        absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
          ((((m + 1) + (m + p)) + 1) + q) rfl
          (CupOne.cup (ambient α β) (m + 1) ((m + 1) + p) (((m + 1) + (m + p)) + 1) (by omega)
            (join α β hκ) (gamma α β r hr h p T)) := by
  have hc := LocalizedCapCupRegradedSource.component_source
    (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) (OriginalFirstHalfZeroCover.cover α β R r η ρ)
    (nearSource α β R) (push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B))
    (join α β hκ) (gamma α β r hr h p T)
    (OriginalFirstHalfLocalizedJoinCap.operation α β R r η ρ hκ)
    (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η good hT)
    (OriginalFirstHalfLocalizedJoinCap.component_source α β R r η ρ hκ)
    (OriginalFirstHalfZeroGammaCap.component_source α β R r hR hr h p T F B η good)
    (((m + 1) + (m + p)) + 1) (by omega) q
  rw [← push_comp, OriginalFirstHalfZeroGammaComparison.source_original] at hc
  exact hc

variable (oldGood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)

theorem component_existing (q : ℕ) :
    (operation α β R r η hR hr h p T hκ F B good hT).component q ≫
      (push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B)).f q =
    eqToHom (congrArg
      (small (ambient α β) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ)).X (by omega :
        ((((m + 1) + (m + p)) + 1) + q) = (m + 1) + (((m + 1) + p) + q))) ≫
      (OriginalFirstHalfLocalizedJoinCap.operation α β R r η ρ hκ).component (((m + 1) + p) + q) ≫
        (OriginalFirstHalfZeroGammaComparison.smallAmbientMap α β R r η ρ).f (((m + 1) + p) + q) ≫
          (FirstInputRotationAmbientCap.operation α β R r hR hr p T (by omega) h F B η oldGood hT).component q := by
  dsimp only [operation, DegreeLoweringRegrade.regrade]
  rw [DegreeLoweringComposition.component]
  simp only [Category.assoc, OriginalFirstHalfZeroGammaCap.operation]
  rw [OriginalFirstHalfZeroGammaComparison.component_compare α β R r η ρ hR hr h p T F B good oldGood hT]
  simp only [← Category.assoc, eqToHom_trans]

end
end Finsler.OriginalFirstHalfSequentialJoinGamma
