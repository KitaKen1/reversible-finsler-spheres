module

public import Finsler.Loop.OriginalFirstHalfNormalizationCochains

/-! The actual normalization primitive cupped with the genuine join
cochain. Its literal original-cylinder boundary error is retained;
only proper and far restrictions are shown to vanish. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizationCup

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f d (φ - ψ) = cochainPullback f d φ - cochainPullback f d ψ :=
  map_sub (((singularCochainComplexZMod2.map f.op).f d).hom) φ ψ

private theorem coboundary_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (ξ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f (d + 1) (cochainCoboundary (ZMod 2) Y d ξ) =
      cochainCoboundary (ZMod 2) X d (cochainPullback f d ξ) :=
  (ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm d (d + 1)) ξ).symm

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)

def normalizedOrder : singularCochainGroup (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1) :=
  CupOne.cup (ambient α β) ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) (by omega)
    (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) (join α β hκ)

def primitive : singularCochainGroup (ZMod 2) (ambient α β) ((m + 1) + (m + p)) :=
  CupOne.cup (ambient α β) (m + p) (m + 1) ((m + 1) + (m + p)) (by omega)
    (OriginalFirstHalfNormalizationCochains.primitive α β r hr h p T) (join α β hκ)

def error : singularCochainGroup (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1) :=
  cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ) -
    (normalizedOrder α β r hr h p T hκ - OriginalFirstHalfCupOrderCochains.originalOrder α β r hr h p T hκ true)

theorem order_join_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) (((m + 1) + (m + p)) + 1)
      (normalizedOrder α β r hr h p T hκ) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inr (join_far_zero α β hκ))

theorem order_cut_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (((m + 1) + (m + p)) + 1)
      (normalizedOrder α β r hr h p T hκ) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _
    (Or.inl (OriginalFirstHalfNormalizationCochains.normalized_cut_far_zero α β r hr h p T))

theorem order_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) (((m + 1) + (m + p)) + 1)
      (normalizedOrder α β r hr h p T hκ) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _
    (Or.inl (OriginalFirstHalfNormalizationCochains.normalized_inner_zero α β r hr h p T))

theorem primitive_join_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _ (Or.inr (join_far_zero α β hκ))

theorem primitive_cut_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _
    (Or.inl (OriginalFirstHalfNormalizationCochains.primitive_cut_far_zero α β r hr h p T))

theorem primitive_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _
    (Or.inl (OriginalFirstHalfNormalizationCochains.primitive_inner_zero α β r hr h p T))

theorem primitive_boundary_join_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) = 0 := by
  rw [coboundary_pullback, primitive_join_far_zero]
  exact map_zero _

theorem primitive_boundary_cut_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) = 0 := by
  rw [coboundary_pullback, primitive_cut_far_zero]
  exact map_zero _

theorem error_join_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 := by
  rw [error, pullback_sub, pullback_sub, primitive_boundary_join_far_zero, order_join_far_zero,
    OriginalFirstHalfCupOrderCochains.original_join_far_zero]
  simp only [sub_self]

theorem error_cut_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 := by
  rw [error, pullback_sub, pullback_sub, primitive_boundary_cut_far_zero, order_cut_far_zero,
    OriginalFirstHalfCupOrderCochains.original_cut_far_zero]
  simp only [sub_self]

variable (R : ℝ) (hR : R ≤ 1 / 2)

def properOrder : singularCochainGroup (ZMod 2) (FirstInputRotationCochains.space α β R r) (((m + 1) + (m + p)) + 1) :=
  CupOne.cup (FirstInputRotationCochains.space α β R r) ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) (by omega)
    (FirstInputRotationNormalizedGamma.normalized α β R r hR hr h p T) (FirstInputRotationCupOne.join α β R r hκ)

def properPrimitive : singularCochainGroup (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p)) :=
  CupOne.cup (FirstInputRotationCochains.space α β R r) (m + p) (m + 1) ((m + 1) + (m + p)) (by omega)
    (FirstInputRotationNormalizedGamma.primitive α β R r hR hr h p T) (FirstInputRotationCupOne.join α β R r hκ)

theorem source_order :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (((m + 1) + (m + p)) + 1)
      (normalizedOrder α β r hr h p T hκ) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (((m + 1) + (m + p)) + 1)
      (properOrder α β r hr h p T hκ R hR) := by
  rw [normalizedOrder, CupCapOrder.naturality,
    OriginalFirstHalfNormalizationCochains.normalized_source α β r hr h p T R hR,
    OriginalFirstHalfCupOrderCochains.source_join α β R r hκ, ← CupCapOrder.naturality]
  rfl

theorem source_primitive :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + (m + p))
      (properPrimitive α β r hr h p T hκ R hR) := by
  rw [primitive, CupCapOrder.naturality,
    OriginalFirstHalfNormalizationCochains.primitive_source α β r hr h p T R hR,
    OriginalFirstHalfCupOrderCochains.source_join α β R r hκ, ← CupCapOrder.naturality]
  rfl

theorem source_primitive_boundary :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
        (properPrimitive α β r hr h p T hκ R hR)) := by
  rw [coboundary_pullback, source_primitive, coboundary_pullback]

theorem proper_closed (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) (((m + 1) + (m + p)) + 1)
      (properOrder α β r hr h p T hκ R hR) = 0 :=
  CupCapOrder.closed _ _ _ _ (by omega) _ _
    (FirstInputRotationNormalizedGamma.normalized_closed α β R r hR hr h p T hT)
    (FirstInputRotationCupOne.join_closed α β R r hκ)

theorem proper_boundary (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (properPrimitive α β r hr h p T hκ R hR) =
    properOrder α β r hr h p T hκ R hR -
      OriginalFirstHalfCupOrderCochains.properOrder α β R r hR hr h p T hκ true :=
  NormalizedCupBoundary.normalization_boundary _ (m + p) ((m + 1) + p) (m + 1) ((m + 1) + (m + p))
    (by omega) (by omega) _ _ (FirstInputRotationCupOne.gamma_closed α β R r hR hr h p T hT)
    (FirstInputRotationCupOne.join_closed α β R r hκ)

include hR in
theorem error_source_zero (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 := by
  rw [error, pullback_sub, pullback_sub, source_primitive_boundary α β r hr h p T hκ R hR,
    source_order α β r hr h p T hκ R hR,
    OriginalFirstHalfCupOrderCochains.source_order α β R r hR hr h p T hκ true,
    proper_boundary α β r hr h p T hκ R hR hT, pullback_sub, sub_self]

include hR in
theorem source_order_boundary_zero (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) ((((m + 1) + (m + p)) + 1) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1)
        (normalizedOrder α β r hr h p T hκ)) = 0 := by
  rw [coboundary_pullback, source_order α β r hr h p T hκ R hR]
  exact pullback_closed _ _ _ (proper_closed α β r hr h p T hκ R hR hT)

variable (F : ReversibleMetric (m + 1)) (L : ℝ)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

include hshort in
theorem proper_order_short_zero :
    cochainPullback (SupportedCap.subspaceMap (FirstInputRotationCochains.space α β R r)
      (TestedCupOneSupport.short F (FirstInputRotationCochains.testedMap α β R r hR hr) L))
      (((m + 1) + (m + p)) + 1) (properOrder α β r hr h p T hκ R hR) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _
    (Or.inl (FirstInputRotationNormalizedGamma.normalized_short_zero α β R r hR hr h p T F L hshort))

include hshort in
theorem proper_primitive_short_zero :
    cochainPullback (SupportedCap.subspaceMap (FirstInputRotationCochains.space α β R r)
      (TestedCupOneSupport.short F (FirstInputRotationCochains.testedMap α β R r hR hr) L))
      ((m + 1) + (m + p)) (properPrimitive α β r hr h p T hκ R hR) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ (by omega) _ _
    (Or.inl (FirstInputRotationNormalizedGamma.primitive_short_zero α β R r hR hr h p T F L hshort))

include hshort in
theorem proper_boundary_short_zero :
    cochainPullback (SupportedCap.subspaceMap (FirstInputRotationCochains.space α β R r)
      (TestedCupOneSupport.short F (FirstInputRotationCochains.testedMap α β R r hR hr) L))
      (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
        (properPrimitive α β r hr h p T hκ R hR)) = 0 :=
  TestedCupOneSupport.coboundary_zero _ _ _ _ _
    (proper_primitive_short_zero α β r hr h p T hκ R hR F L hshort)

end
end Finsler.OriginalFirstHalfNormalizationCup
