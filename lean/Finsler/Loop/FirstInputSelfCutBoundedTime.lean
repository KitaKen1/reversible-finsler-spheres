module

public import Finsler.Loop.FirstInputSelfCutBoundedOperations

/-! Genuine single-input raw and normalized time operations whose
actual retained output lies in length<a-L+3epsilon. Their true proper
and common-input-section components recover the previous operators. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedTime

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)


def operation (v : Bool) := RegradedSingleCapTime.operation (TopCat.of P)
  (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
  (OriginalFirstHalfFactorwiseCover.first_univ hσ)
  (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
  (m + p) ((m + 1) + p) (by omega)
  (FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA v)
  (inner α δ) (FirstInputSelfCutTime.cochain α r hr h p T v) (FirstInputSelfCutTime.inner_zero α r hr h p T v)
  (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
  (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
  (FirstInputSelfCutBoundedOperations.operation_source α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA v)
  (fun x => show SupportedSelfCut.distance (m + 1) (0, α x) ≤ δ from (UniformSelfCutCollar.distance_zero α x).le.trans h.1.le)
  (fun x => show SupportedSelfCut.distance (m + 1) (1, α x) ≤ δ from (UniformSelfCutCollar.distance_one α x).le.trans h.1.le)

theorem component_normal (v : Bool) (q : ℕ) :
    (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA v).component q =
    AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      eqToHom (congrArg (chains (ambient α)).X (show ((m + p) + q) + 1 = ((m + 1) + p) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + 1) + p) + q) ≫
      (FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA v).component q := rfl

theorem component_to_proper (v : Bool) (q : ℕ) :
    (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA v).component q ≫
      (FirstInputSelfCutBoundedSpace.toProperSmall α r hr F (a - L + 3 * ε) κ).f q =
    (FirstInputSelfCutTime.operation α r hr κ h p T hT σ hσ firstIndex hfirst v).component q := by
  rw [component_normal, FirstInputSelfCutTime.component_normal]
  simp only [Category.assoc]
  rw [FirstInputSelfCutBoundedOperations.operation_to_proper]
  rfl

def retained (v : Bool) :=
  (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA v).post
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
      push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε)))

def sectioned (v : Bool) :=
  (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA v).pre
    (TauCeti.smallSingularRetraction (X := TopCat.of P) coeff
      (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ))
      (CommonPrismRefinement.endpointCover_open (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ))
      (CommonPrismRefinement.endpointCover_univ (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_univ hσ)) ≫
      inclusion (TopCat.of P) (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)))

theorem sectioned_component_to_proper (v : Bool) (q : ℕ) :
    (sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA v).component q ≫
      (FirstInputSelfCutBoundedSpace.toProperSmall α r hr F (a - L + 3 * ε) κ).f q =
    (FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst v).component q := by
  dsimp only [sectioned, FirstInputSelfCutTime.sectioned, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, component_to_proper]

end
end Finsler.FirstInputSelfCutBoundedTime
