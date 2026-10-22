module

public import Finsler.Loop.FirstInputSelfCutBoundedCarrierCap
public import Finsler.Loop.FirstInputSelfCutNormalizationCap

/-! Instantiate actual raw, normalized and primitive cut caps in
the individual length<a-L+3epsilon proper carrier using the literal
cochains and their proved tested-short support. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedOperations

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
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)

theorem cochain_far (v : Bool) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + 1) + p)
      (FirstInputSelfCutTime.cochain α r hr h p T v) = 0 := by
  cases v
  · exact raw_far_zero α r hr h p T
  · exact normalized_far_zero α r hr h p T

include hT in
theorem cochain_proper_boundary (v : Bool) :
    cochainPullback (source α r) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α) ((m + 1) + p) (FirstInputSelfCutTime.cochain α r hr h p T v)) = 0 := by
  cases v
  · exact FirstInputSelfCutOperations.source_boundary_raw α r hr h p T hT
  · exact FirstInputSelfCutOperations.source_boundary_normalized α r hr h p T hT

include hshortT in
theorem proper_short (v : Bool) :
    cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) ((m + 1) + p)
      (cochainPullback (source α r) ((m + 1) + p) (FirstInputSelfCutTime.cochain α r hr h p T v)) = 0 := by
  cases v
  · simpa only [FirstInputSelfCutTime.cochain, Bool.false_eq_true, ↓reduceIte, source_raw] using
      OriginalFirstHalfCutNormalizedFactors.cutGamma_short_zero α r hr h p T F L hshortT
  · simpa only [FirstInputSelfCutTime.cochain, ↓reduceIte, source_normalized] using
      OriginalFirstHalfCutNormalizedFactors.normalized_short_zero α r hr h p T F L hshortT

def operation (v : Bool) := FirstInputSelfCutBoundedCarrierCap.operation α r hr κ ρ ((m + 1) + p)
  (FirstInputSelfCutTime.cochain α r hr h p T v) (cochain_far α r hr h p T v)
  F ε a L σ hε hradius hsmall firstIndex hfirst (proper_short α r hr h p T F L hshortT v) hA
  (cochain_proper_boundary α r hr h p T hT v)

theorem operation_source (v : Bool) (q : ℕ) :
    (operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA v).component q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl (FirstInputSelfCutTime.cochain α r hr h p T v) :=
  FirstInputSelfCutBoundedCarrierCap.component_source α r hr κ ρ _ _ (cochain_far α r hr h p T v)
    F ε a L σ hε hradius hsmall firstIndex hfirst (proper_short α r hr h p T F L hshortT v) hA q

theorem operation_to_proper (v : Bool) (q : ℕ) :
    (operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA v).component q ≫
      (FirstInputSelfCutBoundedSpace.toProperSmall α r hr F (a - L + 3 * ε) κ).f q =
    (FirstInputSelfCutTime.refinedCap α r hr κ h p T hT σ firstIndex hfirst v).component q := by
  have hh := FirstInputSelfCutBoundedCarrierCap.component_to_proper α r hr κ ρ _ _ (cochain_far α r hr h p T v)
    F ε a L σ hε hradius hsmall firstIndex hfirst (proper_short α r hr h p T F L hshortT v) hA q
  cases v <;> exact hh

include hshortT in
theorem primitive_short :
    cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) (m + p)
      (cochainPullback (source α r) (m + p) (primitive α r hr h p T)) = 0 := by
  rw [source_primitive]
  exact OriginalFirstHalfCutNormalizedFactors.primitive_short_zero α r hr h p T F L hshortT

def primitiveCap (q : ℕ) := FirstInputSelfCutBoundedCarrierCap.component α r hr κ ρ (m + p)
  (primitive α r hr h p T) (primitive_far_zero α r hr h p T)
  F ε a L σ hε hradius hsmall firstIndex hfirst (primitive_short α r hr h p T F L hshortT) hA q

theorem primitive_source (q : ℕ) :
    primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((m + p) + q) ≫
      absoluteChain (ambient α) (m + p) q ((m + p) + q) rfl (primitive α r hr h p T) :=
  FirstInputSelfCutBoundedCarrierCap.component_source α r hr κ ρ _ _ (primitive_far_zero α r hr h p T)
    F ε a L σ hε hradius hsmall firstIndex hfirst (primitive_short α r hr h p T F L hshortT) hA q

theorem primitive_to_proper (q : ℕ) :
    primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q ≫
      (FirstInputSelfCutBoundedSpace.toProperSmall α r hr F (a - L + 3 * ε) κ).f q =
    (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f ((m + p) + q) ≫
      FirstInputSelfCutNormalizationCap.primitiveCap α r hr κ h p T q :=
  FirstInputSelfCutBoundedCarrierCap.component_to_proper α r hr κ ρ _ _ (primitive_far_zero α r hr h p T)
    F ε a L σ hε hradius hsmall firstIndex hfirst (primitive_short α r hr h p T F L hshortT) hA q

end
end Finsler.FirstInputSelfCutBoundedOperations
