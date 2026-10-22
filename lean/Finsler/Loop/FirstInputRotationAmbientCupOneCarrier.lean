module

public import Finsler.Loop.FirstInputRotationAmbientCupOne
public import Finsler.Loop.FirstInputRotationAmbientSupportedCap

/-! Actual ambient far and inner support of the entire cup-one
primitive, together with the literal proper restriction of its
coboundary. No ambient tested-extension closure is used. -/

@[expose] public section
namespace Finsler.FirstInputRotationAmbientCupOneCarrier

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationAmbientCover Finsler.FirstInputRotationAmbientCupOne

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem gamma_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)) ((m + 1) + p)
      (gamma α β R r hR hr h p T) = 0 := by
  rw [gamma, cochainCup_naturality, thom_far_zero α β R hR (by omega) h, cochainCup_zero_left]

theorem primitive_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)) ((m + 1) + (m + p))
      (primitive α β R r hR hr h p T hκ) = 0 :=
  CupOne.restriction_zero _ (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega) _ _
    (Or.inr (gamma_far_zero α β R r hR hr h p T))

theorem primitive_boundary_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β R) ((m + 1) + (m + p))
        (primitive α β R r hR hr h p T hκ)) = 0 :=
  FirstInputRotationAmbientSupportedCap.far_coboundary_zero α β R ρ ((m + 1) + (m + p))
    (primitive α β R r hR hr h p T hκ) (primitive_far_zero α β R r hR hr h p T hκ)

theorem source_primitive_boundary {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (source α β R r) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β R) ((m + 1) + (m + p))
        (primitive α β R r hR hr h p T hκ)) =
      cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
        (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ) := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (source α β R r).op).comm
      ((m + 1) + (m + p)) (((m + 1) + (m + p)) + 1)) (primitive α β R r hR hr h p T hκ)
  change cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
    (cochainPullback (source α β R r) ((m + 1) + (m + p)) (primitive α β R r hR hr h p T hκ)) = _ at he
  rw [source_primitive] at he
  exact he.symm

def inner (δ : ℝ) : Set (ambient α β R) := {z | gap α β R z ≤ δ}

theorem primitive_inner_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β R) (inner α β R δ)) ((m + 1) + (m + p))
      (primitive α β R r hR hr h p T hκ) = 0 := by
  apply CupOne.restriction_zero _ (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega) _ _ (Or.inr ?_)
  rw [gamma, cochainCup_naturality]
  have ht : cochainPullback (SupportedCap.subspaceMap (ambient α β R) (inner α β R δ)) (m + 1)
      (ambientThom α β R hR (by omega) h) = 0 := by
    apply pullback_support (ambientEvaluation α β R hR) (inner α β R δ)
      {z | SupportedSelfCut.distance (m + 1) z ≤ δ} _ (m + 1)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSelfCut.cocycle_small_zero (m + 1) (by omega) h)
    intro z hz
    change SupportedSelfCut.distance (m + 1) (ambientEvaluation α β R hR z) ≤ δ
    rw [evaluation_gap]
    exact hz
  rw [ht, cochainCup_zero_left]

end
end Finsler.FirstInputRotationAmbientCupOneCarrier
