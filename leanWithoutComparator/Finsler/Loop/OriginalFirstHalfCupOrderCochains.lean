module

public import Finsler.Loop.OriginalFirstHalfJointCochains
public import Finsler.Loop.CupCapOrder

/-! Both actual cup orders, their literal proper source restrictions,
short support, local closure and real sequential cap formulas. False
is spatial join first; true is the original tested cut cup first. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCupOrderCochains

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedSelfCut Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)

def originalOrder : Bool → singularCochainGroup (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1)
  | false => CupOne.cup (ambient α β) (m + 1) ((m + 1) + p) (((m + 1) + (m + p)) + 1) (by omega)
      (join α β hκ) (gamma α β r hr h p T)
  | true => CupOne.cup (ambient α β) ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) (by omega)
      (gamma α β r hr h p T) (join α β hκ)

def properOrder : Bool → singularCochainGroup (ZMod 2) (FirstInputRotationCochains.space α β R r) (((m + 1) + (m + p)) + 1)
  | false => CupOne.cup (FirstInputRotationCochains.space α β R r) (m + 1) ((m + 1) + p)
      (((m + 1) + (m + p)) + 1) (by omega) (FirstInputRotationCupOne.join α β R r hκ)
      (FirstInputRotationCupOne.gamma α β R r hR hr h p T)
  | true => CupOne.cup (FirstInputRotationCochains.space α β R r) ((m + 1) + p) (m + 1)
      (((m + 1) + (m + p)) + 1) (by omega) (FirstInputRotationCupOne.gamma α β R r hR hr h p T)
      (FirstInputRotationCupOne.join α β R r hκ)

theorem source_join :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (m + 1) (join α β hκ) =
      cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (m + 1)
        (FirstInputRotationCupOne.join α β R r hκ) := by
  rw [OriginalFirstHalfJointCover.source_near, pullback_comp, join_near, ← pullback_comp,
    OriginalFirstHalfJointCochains.rotating_square, pullback_comp, FirstInputRotationAmbientCupOne.source_join]

theorem source_order (b : Bool) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (((m + 1) + (m + p)) + 1)
      (originalOrder α β r hr h p T hκ b) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (((m + 1) + (m + p)) + 1)
      (properOrder α β R r hR hr h p T hκ b) := by
  cases b <;> dsimp only [originalOrder, properOrder]
  all_goals rw [CupCapOrder.naturality, source_join,
    OriginalFirstHalfJointCochains.source_gamma α β R r hR hr h p T, ← CupCapOrder.naturality]

theorem proper_closed (b : Bool)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) (((m + 1) + (m + p)) + 1)
      (properOrder α β R r hR hr h p T hκ b) = 0 := by
  cases b
  · exact CupCapOrder.closed _ _ _ _ (by omega) _ _
      (FirstInputRotationCupOne.join_closed α β R r hκ) (FirstInputRotationCupOne.gamma_closed α β R r hR hr h p T hT)
  · exact CupCapOrder.closed _ _ _ _ (by omega) _ _
      (FirstInputRotationCupOne.gamma_closed α β R r hR hr h p T hT) (FirstInputRotationCupOne.join_closed α β R r hκ)

theorem proper_short_zero (b : Bool) (F : ReversibleMetric (m + 1)) (L : ℝ)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0) :
    cochainPullback (SupportedCap.subspaceMap (FirstInputRotationCochains.space α β R r)
      (TestedCupOneSupport.short F (FirstInputRotationCochains.testedMap α β R r hR hr) L))
      (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ b) = 0 := by
  have hg := TestedCupOneSupport.gamma_zero F (FirstInputRotationCochains.testedMap α β R r hR hr) L
    (m + 1) p (FirstInputRotationCochains.thom α β R r hR hr (by omega) h) T hshort
  cases b
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inr hg)
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inl hg)

theorem original_join_far_zero (b : Bool) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) (((m + 1) + (m + p)) + 1)
      (originalOrder α β r hr h p T hκ b) = 0 := by
  cases b
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inl (join_far_zero α β hκ))
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inr (join_far_zero α β hκ))

theorem original_cut_far_zero (b : Bool) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (((m + 1) + (m + p)) + 1)
      (originalOrder α β r hr h p T hκ b) = 0 := by
  cases b
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inr (gamma_cut_far_zero α β r hr h p T))
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inl (gamma_cut_far_zero α β r hr h p T))

theorem gamma_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) ((m + 1) + p)
      (gamma α β r hr h p T) = 0 := by
  rw [gamma, FirstInputRotationZeroTimeFactors.originalGamma, cochainCup_naturality, cochainCup_naturality]
  have ht : cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) (m + 1)
      (cochainPullback (firstInput α β) (m + 1) (FirstInputRotationZeroTimeFactors.originalThom α h)) = 0 := by
    rw [FirstInputRotationZeroTimeFactors.originalThom, AnnularSelfCut.familyCocycle,
      ← pullback_comp (firstInput α β) (AnnularSelfCut.familyMap α)]
    apply pullback_support (firstInput α β ≫ AnnularSelfCut.familyMap α) (inner α β δ)
      {z | distance (m + 1) z ≤ δ} _ (m + 1) (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSelfCut.cocycle_small_zero (m + 1) (by omega) h)
    intro z hz
    exact hz
  rw [ht, cochainCup_zero_left]

theorem original_inner_zero (b : Bool) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) (((m + 1) + (m + p)) + 1)
      (originalOrder α β r hr h p T hκ b) = 0 := by
  cases b
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inr (gamma_inner_zero α β r hr h p T))
  · exact CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inl (gamma_inner_zero α β r hr h p T))

include hR in
theorem source_coboundary_zero (b : Bool)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) ((((m + 1) + (m + p)) + 1) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1)
        (originalOrder α β r hr h p T hκ b)) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (OriginalFirstHalfJointCover.source α β R r).op).comm
      (((m + 1) + (m + p)) + 1) ((((m + 1) + (m + p)) + 1) + 1)) (originalOrder α β r hr h p T hκ b)
  change cochainCoboundary (ZMod 2) (TopCat.of (FirstInputRotatingCut.source α β R r)) (((m + 1) + (m + p)) + 1)
    (cochainPullback (OriginalFirstHalfJointCover.source α β R r) (((m + 1) + (m + p)) + 1)
      (originalOrder α β r hr h p T hκ b)) = _ at he
  rw [source_order α β R r hR hr h p T hκ b] at he
  exact he.symm.trans (pullback_closed (FirstInputRotationEndpoints.stage α β R r 0) _ _
    (proper_closed α β R r hR hr h p T hκ b hT))

theorem cap_order_raw (b : Bool) (q : ℕ) :
    absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
      (originalOrder α β r hr h p T hκ b) =
    match b with
    | false => absoluteChain (ambient α β) (m + 1) (((m + 1) + p) + q)
        ((((m + 1) + (m + p)) + 1) + q) (by omega) (join α β hκ) ≫
          absoluteChain (ambient α β) ((m + 1) + p) q (((m + 1) + p) + q) rfl (gamma α β r hr h p T)
    | true => absoluteChain (ambient α β) ((m + 1) + p) ((m + 1) + q)
        ((((m + 1) + (m + p)) + 1) + q) (by omega) (gamma α β r hr h p T) ≫
          absoluteChain (ambient α β) (m + 1) q ((m + 1) + q) rfl (join α β hκ) := by
  cases b
  · exact (CupCapOrder.cap_cup _ _ _ _ _ (by omega) _ _).symm
  · exact (CupCapOrder.cap_cup _ _ _ _ _ (by omega) _ _).symm

end
end Finsler.OriginalFirstHalfCupOrderCochains
