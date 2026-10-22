module

public import Finsler.Loop.SingleCutThomRepresentativeError
public import Finsler.Loop.FirstInputSelfCutBoundedOperations

/-! Genuine canonical Thom/tested cap and annular comparison primitive
inside the same individual length bound. The primitive's full cap
boundary is the actual annular/canonical cap difference. -/

@[expose] public section
namespace Finsler.SingleCutBoundedCanonicalThomCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open Finsler.SingleCutCanonicalThomCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hm : 1 ≤ m) (hρ2 : ρ ≤ 2)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)

include hshortT in
theorem gamma_short :
    cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) ((m + 1) + p)
      (cochainPullback (source α r) ((m + 1) + p) (canonicalGamma α r hr h p T)) = 0 := by
  rw [source_gamma]
  exact properGamma_short_zero α r hr h p T F L hshortT

def operation := FirstInputSelfCutBoundedCarrierCap.operation α r hr κ ρ ((m + 1) + p)
  (canonicalGamma α r hr h p T) (gamma_far_zero α r hr h p T)
  F ε a L σ hε hradius hsmall firstIndex hfirst (gamma_short α r hr h p T F L hshortT) hA
  (gamma_proper_boundary α r hr h p T hT)

theorem operation_source (q : ℕ) :
    (operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).component q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl (canonicalGamma α r hr h p T) :=
  FirstInputSelfCutBoundedCarrierCap.component_source α r hr κ ρ _ _ (gamma_far_zero α r hr h p T)
    F ε a L σ hε hradius hsmall firstIndex hfirst (gamma_short α r hr h p T F L hshortT) hA q

include hshortT in
theorem primitive_short :
    cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) (m + p)
      (cochainPullback (source α r) (m + p) (comparisonPrimitive α r hr h p T hm hρ2)) = 0 := by
  rw [SingleCutCanonicalThomCochains.source_primitive]
  exact properPrimitive_short_zero α r hr h p T hm hρ2 F L hshortT

def primitiveCap (q : ℕ) := FirstInputSelfCutBoundedCarrierCap.component α r hr κ ρ (m + p)
  (comparisonPrimitive α r hr h p T hm hρ2) (SingleCutCanonicalThomCochains.primitive_far_zero α r hr h p T hm hρ2)
  F ε a L σ hε hradius hsmall firstIndex hfirst (primitive_short α r hr h p T hm hρ2 F L hshortT) hA q

theorem primitive_source (q : ℕ) :
    primitiveCap α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((m + p) + q) ≫
      absoluteChain (ambient α) (m + p) q ((m + p) + q) rfl (comparisonPrimitive α r hr h p T hm hρ2) :=
  FirstInputSelfCutBoundedCarrierCap.component_source α r hr κ ρ _ _ (SingleCutCanonicalThomCochains.primitive_far_zero α r hr h p T hm hρ2)
    F ε a L σ hε hradius hsmall firstIndex hfirst (primitive_short α r hr h p T hm hρ2 F L hshortT) hA q

def boundaryCap (q : ℕ) :=
  eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
    (show ((m + p) + 1) + q = ((m + 1) + p) + q by omega)) ≫
  ((FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA false).component q -
    (operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).component q)

theorem boundary_source (q : ℕ) :
    boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + p) + 1) + q) ≫
      absoluteChain (ambient α) ((m + p) + 1) q (((m + p) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α) (m + p) (comparisonPrimitive α r hr h p T hm hρ2)) := by
  have he := SingleCutThomRepresentativeError.error_small_cap_zero α r hr h p T hm hρ2 hT κ q
  have hi := congrArg (fun f => f.f (((m + p) + 1) + q))
    (SmallRefinementComparison.refinement_inclusion (X := ambient α)
      (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst)
  simp only [HomologicalComplex.comp_f] at hi
  have hz : (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + p) + 1) + q) ≫
      absoluteChain (ambient α) ((m + p) + 1) q (((m + p) + 1) + q) rfl
        (SingleCutThomRepresentativeError.error α r hr h p T hm hρ2) = 0 := by
    rw [← hi, Category.assoc, he, comp_zero]
  rw [SingleCutThomRepresentativeError.error, SupportedCapCochain.absolute_sub, Preadditive.comp_sub] at hz
  have hh := sub_eq_zero.mp hz
  rw [SingleCutThomRepresentativeError.difference, CochainInputRegrade.small_cap] at hh
  have hb :
      ((FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA false).component q -
        (operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).component q) ≫
          (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
      (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + 1) + p) + q) ≫
        absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl
          (raw α r hr h p T - canonicalGamma α r hr h p T) := by
    rw [Preadditive.sub_comp, FirstInputSelfCutBoundedOperations.operation_source, operation_source,
      SupportedCapCochain.absolute_sub, Preadditive.comp_sub]
    rfl
  dsimp only [boundaryCap]
  rw [Category.assoc, hb]
  exact hh.symm

theorem boundary (q : ℕ) :
    primitiveCap α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA (q + 1) ≫
      (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q =
    (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).d ((m + p) + (q + 1)) ((m + p) + q) ≫
      primitiveCap α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q -
    eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
      (show (m + p) + (q + 1) = ((m + p) + 1) + q by omega)) ≫
      boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q :=
  LiftedCapCochainBoundary.boundary (OriginalFirstHalfFactorwiseCover.first σ)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
    (m + p) (comparisonPrimitive α r hr h p T hm hρ2)
    (primitiveCap α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (primitive_source α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (boundary_source α r hr κ h p T hm hρ2 hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA) q

end
end Finsler.SingleCutBoundedCanonicalThomCap
