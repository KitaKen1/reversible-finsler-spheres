module

public import Finsler.Loop.FirstInputSelfCutCochains
public import Finsler.Loop.CupCapOrder
public import Finsler.Topology.AnnularCutComparison

/-! Actual canonical Thom/tested cup and the supported annular comparison
primitive. The tested zero extension is used literally, without assuming
that it is closed on the entire cylinder. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalThomCochains

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.FirstInputSelfCutCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def canonicalThom := cochainPullback (AnnularSelfCut.familyMap α) (m + 1)
  (NormalizedSelfCut.cocycle (m + 1) (by omega) (h.1.trans h.2.2))

def canonicalGamma := CupOne.cup (ambient α) (m + 1) p ((m + 1) + p) rfl
  (canonicalThom α h) (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)

def properGamma := CupOne.cup (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
  (m + 1) p ((m + 1) + p) rfl
  (cochainPullback (FirstInputRotationOriginalFactors.originalEvaluation α r) (m + 1)
    (NormalizedSelfCut.cocycle (m + 1) (by omega) (h.1.trans h.2.2)))
  (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T)

theorem source_gamma : cochainPullback (source α r) ((m + 1) + p)
    (canonicalGamma α r hr h p T) = properGamma α r hr h p T := by
  rw [canonicalGamma, CupCapOrder.naturality, canonicalThom, ← pullback_comp, evaluation_square,
    FirstInputRotationZeroTimeFactors.originalTested]
  rw [show source α r = SupportedCap.subspaceMap (ambient α) (CompactRotatedCutData.source α r) from rfl,
    TubeCochainExtension.restriction]
  rfl

theorem canonicalThom_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) (m + 1)
      (canonicalThom α h) = 0 :=
  pullback_support (AnnularSelfCut.familyMap α) (far α ρ) (SupportedSelfCut.exterior (m + 1) ρ)
    (fun _ hz => hz) (m + 1) _
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) (h.1.trans h.2.2))

theorem gamma_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + 1) + p)
      (canonicalGamma α r hr h p T) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ rfl _ _ (Or.inl (canonicalThom_far_zero α h))

variable (hm : 1 ≤ m) (hρ2 : ρ ≤ 2)

def thomPrimitive : singularCochainGroup (ZMod 2) (ambient α) m :=
  cochainPullback (AnnularSelfCut.familyMap α) m
    (AnnularSelfCut.primitive (m + 1) (by omega) h hρ2)

def comparisonPrimitive := CupOne.cup (ambient α) m p (m + p) rfl
  (thomPrimitive α h hm hρ2) (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)

def properPrimitive := CupOne.cup (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
  m p (m + p) rfl
  (cochainPullback (FirstInputRotationOriginalFactors.originalEvaluation α r) m
    (AnnularSelfCut.primitive (m + 1) (by omega) h hρ2))
  (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T)

theorem source_primitive : cochainPullback (source α r) (m + p)
    (comparisonPrimitive α r hr h p T hm hρ2) = properPrimitive α r hr h p T hm hρ2 := by
  rw [comparisonPrimitive, CupCapOrder.naturality, thomPrimitive, ← pullback_comp, evaluation_square,
    FirstInputRotationZeroTimeFactors.originalTested]
  rw [show source α r = SupportedCap.subspaceMap (ambient α) (CompactRotatedCutData.source α r) from rfl,
    TubeCochainExtension.restriction]
  rfl

theorem thomPrimitive_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) m
      (thomPrimitive α h hm hρ2) = 0 :=
  pullback_support (AnnularSelfCut.familyMap α) (far α ρ) (SupportedSelfCut.exterior (m + 1) ρ)
    (fun _ hz => hz) m _
    (AnnularCutComparison.primitive_supported (m + 1) (by omega) h hρ2)

theorem primitive_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) (m + p)
      (comparisonPrimitive α r hr h p T hm hρ2) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ rfl _ _ (Or.inl (thomPrimitive_far_zero α h hm hρ2))

variable (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hT in
theorem properGamma_closed :
    cochainCoboundary (ZMod 2) (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) ((m + 1) + p)
      (properGamma α r hr h p T) = 0 :=
  CupCapOrder.closed _ _ _ _ rfl _ _
    (pullback_closed _ _ _ (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) (h.1.trans h.2.2)))
    (pullback_closed _ _ _ hT)

include hT in
theorem gamma_proper_boundary :
    cochainPullback (source α r) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α) ((m + 1) + p) (canonicalGamma α r hr h p T)) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (source α r).op).comm ((m + 1) + p) (((m + 1) + p) + 1))
    (canonicalGamma α r hr h p T)
  change cochainCoboundary (ZMod 2) (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) ((m + 1) + p)
    (cochainPullback (source α r) ((m + 1) + p) (canonicalGamma α r hr h p T)) = _ at he
  rw [source_gamma, properGamma_closed α r hr h p T hT] at he
  exact he.symm

variable (F : ReversibleMetric (m + 1)) (L : ℝ)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

include hshort in
theorem properGamma_short_zero :
    cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L))
      ((m + 1) + p) (properGamma α r hr h p T) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ rfl _ _ (Or.inr
    (TestedCupOneSupport.tested_zero F (FirstInputRotationOriginalFactors.originalTester α r hr) L p T hshort))

include hshort in
theorem properPrimitive_short_zero :
    cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L))
      (m + p) (properPrimitive α r hr h p T hm hρ2) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ rfl _ _ (Or.inr
    (TestedCupOneSupport.tested_zero F (FirstInputRotationOriginalFactors.originalTester α r hr) L p T hshort))

end
end Finsler.SingleCutCanonicalThomCochains
