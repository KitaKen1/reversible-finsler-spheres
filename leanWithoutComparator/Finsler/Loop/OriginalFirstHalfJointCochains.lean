module

public import Finsler.Loop.OriginalFirstHalfJointCover

/-! The original-input cochains restrict literally to the proper
rotation-zero model. Their coboundaries keep both far supports, and
the genuine cup-one error vanishes on the actual joint proper space. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfJointCochains

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

private theorem coboundary_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (ξ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f (d + 1) (cochainCoboundary (ZMod 2) Y d ξ) =
      cochainCoboundary (ZMod 2) X d (cochainPullback f d ξ) :=
  (ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm d (d + 1)) ξ).symm

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)

theorem rotating_square :
    SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (FirstInputRotatingCut.source α β R r) ≫ rotatingZero α β R =
    FirstInputRotationEndpoints.stage α β R r 0 ≫ FirstInputRotationAmbientCover.source α β R r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem source_gamma :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) ((m + 1) + p) (gamma α β r hr h p T) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + p)
      (FirstInputRotationCupOne.gamma α β R r hR hr h p T) := by
  rw [OriginalFirstHalfJointCover.source_near, pullback_comp,
    gamma_near α β r hr h p T R hR, ← pullback_comp, rotating_square, pullback_comp,
    FirstInputRotationAmbientCupOne.source_gamma]

theorem source_primitive {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + (m + p))
      (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ) := by
  rw [OriginalFirstHalfJointCover.source_near, pullback_comp,
    primitive_near α β r hr h p T R hR, ← pullback_comp, rotating_square, pullback_comp,
    FirstInputRotationAmbientCupOne.source_primitive]

theorem source_primitive_boundary {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
        (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ)) := by
  rw [coboundary_pullback, source_primitive α β R r hR hr h p T hκ, coboundary_pullback]

theorem primitive_boundary_join_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) = 0 := by
  rw [coboundary_pullback, primitive_join_far_zero]
  exact map_zero _

theorem primitive_boundary_cut_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) = 0 := by
  rw [coboundary_pullback, primitive_cut_far_zero]
  exact map_zero _

theorem primitive_boundary_inner_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) = 0 := by
  rw [coboundary_pullback, primitive_inner_zero]
  exact map_zero _

theorem error_join_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 :=
  CupOne.restriction_zero _ (m + 1) (((m + 1) + p) + 1) (((m + 1) + (m + p)) + 1) (by omega) _ _
    (Or.inl (join_far_zero α β hκ))

theorem error_cut_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 := by
  apply CupOne.restriction_zero _ (m + 1) (((m + 1) + p) + 1) (((m + 1) + (m + p)) + 1) (by omega) _ _ (Or.inr ?_)
  rw [coboundary_pullback, gamma_cut_far_zero]
  exact map_zero _

include hR in
theorem error_proper_zero {κ : ℝ} (hκ : 0 < κ)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 := by
  apply CupOne.restriction_zero _ (m + 1) (((m + 1) + p) + 1) (((m + 1) + (m + p)) + 1) (by omega) _ _ (Or.inr ?_)
  rw [coboundary_pullback, source_gamma α β R r hR hr h p T]
  exact pullback_closed (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + p) _
    (FirstInputRotationCupOne.gamma_closed α β R r hR hr h p T hT)

end
end Finsler.OriginalFirstHalfJointCochains
