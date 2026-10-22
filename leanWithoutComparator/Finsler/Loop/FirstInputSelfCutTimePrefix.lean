module

public import Finsler.Loop.FirstInputSelfCutTime
public import Finsler.Loop.FirstFactorSectionedPrismSummand

/-! The genuine single-input cut-time component uses precisely the
sectioned first-factor prism timePrefix occurring before the external cross. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutTimePrefix

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (σ : ℝ) (hσ : 0 < σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))

def timePrefix (i : ℕ) :=
  FirstFactorSectionedPrismSummand.firstPrefix (X := TopCat.of P)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
    (OriginalFirstHalfFactorwiseCover.first_univ hσ) ((m + p) + i) ≫
  eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
    (show (m + p) + i + 1 = ((m + 1) + p) + i by omega))

theorem prefix_normal (i : ℕ) :
    timePrefix α p σ hσ i =
    (TauCeti.smallSingularRetraction (X := TopCat.of P) coeff
      (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ))
      (CommonPrismRefinement.endpointCover_open (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ))
      (CommonPrismRefinement.endpointCover_univ (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_univ hσ))).f ((m + p) + i) ≫
    (CommonPrismRefinement.prism (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)).hom
      ((m + p) + i) ((m + p) + i + 1) ≫
    eqToHom (congrArg (chains (ambient α)).X
      (show (m + p) + i + 1 = ((m + 1) + p) + i by omega)) ≫
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f
      (((m + 1) + p) + i) := by
  simp only [timePrefix, FirstFactorSectionedPrismSummand.firstPrefix, Category.assoc]
  rw [LocalizedCapCupComponentSource.transport_f]
  omega

theorem sectioned_component (v : Bool) (i : ℕ) :
    (FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst v).component i =
    timePrefix α p σ hσ i ≫
      (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f (((m + 1) + p) + i) ≫
      (FirstInputSelfCutTime.properCap α r hr κ h p T hT v).component i := by
  rw [FirstInputSelfCutTime.sectioned_component, prefix_normal]
  rfl

theorem normalized_component (i : ℕ) :
    (FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst true).component i =
    timePrefix α p σ hσ i ≫
      (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f (((m + 1) + p) + i) ≫
      (FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT).component i :=
  sectioned_component α r hr κ h p T hT σ hσ firstIndex hfirst true i

end
end Finsler.FirstInputSelfCutTimePrefix
