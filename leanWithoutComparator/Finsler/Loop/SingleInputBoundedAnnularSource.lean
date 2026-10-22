module

public import Finsler.Loop.SingleInputAnnularSmallCap
public import Finsler.Loop.FirstInputSelfCutBoundedTime
public import Finsler.Loop.LocalizedCapCupComponentSource

/-! The actual individually bounded raw cap has the real global
annular cut as its ambient CHAIN source, on the original small input.
The actual short output and source carrier are retained. -/

@[expose] public section
namespace Finsler.SingleInputBoundedAnnularSource

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)

def properChain := inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
  (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
  push (FirstInputSelfCutBoundedSpace.toCut α r hr F (a - L + 3 * ε))

def retainedChain := inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
  (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
  push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε))

theorem properChain_source : properChain α r hr κ F ε a L ≫ push (source α r) =
    FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ := by
  rw [properChain, Category.assoc, ← push_comp, FirstInputSelfCutBoundedSpace.source_square]
  rfl

theorem retainedChain_source : retainedChain α r hr κ F ε a L ≫
    push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (a - L + 3 * ε))) =
    properChain α r hr κ F ε a L ≫ push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr)) := by
  have hs : FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε) ≫
      SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (a - L + 3 * ε)) =
    FirstInputSelfCutBoundedSpace.toCut α r hr F (a - L + 3 * ε) ≫
      TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr) := by ext z : 1; rfl
  simp only [retainedChain, properChain, Category.assoc, ← push_comp, hs]

theorem nested_source (q : ℕ) :
    eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
      (show (m + 1) + (p + q) = ((m + 1) + p) + q by omega)) ≫
      (FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall
        firstIndex hfirst hshortT hA false).component q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap (ambient α) (m + 1) p q
        (FirstInputRotationZeroTimeFactors.originalThom α h)
        (FirstInputRotationZeroTimeFactors.originalTested α r hr p T) := by
  rw [FirstInputSelfCutBoundedOperations.operation_source]
  rw [← Category.assoc, LocalizedCapCupComponentSource.transport_f]
  simp only [Category.assoc]
  change _ ≫ eqToHom (congrArg (chains (ambient α)).X
      (show (m + 1) + (p + q) = ((m + 1) + p) + q by omega)) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl
        (cochainCup (m + 1) p (FirstInputRotationZeroTimeFactors.originalThom α h)
          (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)) = _
  rw [CapCupNested.flat_nested]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  omega


theorem proper_component (q : ℕ) :
    eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
      (show (m + 1) + (p + q) = ((m + 1) + p) + q by omega)) ≫
      (FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall
        firstIndex hfirst hshortT hA false).component q ≫
      (properChain α r hr κ F ε a L).f q =
    SingleInputAnnularSmallCap.localCap α r hr κ σ firstIndex hfirst h p T q := by
  have : Mono ((push (source α r)).f q) :=
    SupportedCap.subspacePush_mono (ambient α) (CompactRotatedCutData.source α r) q
  apply (cancel_mono ((push (source α r)).f q)).mp
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, properChain_source,
    SingleInputAnnularSmallCap.localCap_source α r hr κ σ firstIndex hfirst h p T q]
  exact nested_source α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q

variable (hρr : ρ < r)

theorem annular_component (q : ℕ) :
    eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
      (show (m + 1) + (p + q) = ((m + 1) + p) + q by omega)) ≫
      (FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall
        firstIndex hfirst hshortT hA false).component q ≫
      (retainedChain α r hr κ F ε a L).f q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (a - L + 3 * ε)))).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((m + 1) + (p + q)) ≫
      (push (AnnularSelfCut.familyMap α)).f ((m + 1) + (p + q)) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
        (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
      AnnularCutComparison.cut m p h hρr hr.le T hT q := by
  rw [← HomologicalComplex.comp_f, retainedChain_source, HomologicalComplex.comp_f]
  have hp := congrArg (fun f => f ≫ (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr))).f q)
    (proper_component α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q)
  simpa only [Category.assoc] using hp.trans
    (SingleInputAnnularSmallCap.annular_source α r hr κ σ firstIndex hfirst h p T hρr hT q)

end
end Finsler.SingleInputBoundedAnnularSource
