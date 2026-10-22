module

public import Finsler.Loop.OriginalFirstHalfJointSupportedCap
public import Finsler.Loop.OriginalFirstHalfJointCochains
public import Finsler.Loop.LiftedCapCochainBoundary

/-! Genuine primitive/coboundary cap lifts on the original input
cylinder, into the same bounded zero-slice proper domain. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCupOneBounded

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJointSupportedCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {κ : ℝ} (hκ : 0 < κ) (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + (m + p))
    (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ))
  (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ)))

def primitiveCap (q : ℕ) :
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X (((m + 1) + (m + p)) + q) ⟶
      (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  component α β R r hR hr F B η κ ρ ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)
    (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ)
    (primitive_join_far_zero α β r hr h p T hκ) (primitive_cut_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfJointCochains.source_primitive α β R r hR hr h p T hκ) good q

def boundaryCap (q : ℕ) :
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X ((((m + 1) + (m + p)) + 1) + q) ⟶
      (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  component α β R r hR hr F B η κ ρ (((m + 1) + (m + p)) + 1)
    (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ))
    (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ))
    (OriginalFirstHalfJointCochains.primitive_boundary_join_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfJointCochains.primitive_boundary_cut_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfJointCochains.source_primitive_boundary α β R r hR hr h p T hκ) goodδ q

theorem primitiveCap_source (q : ℕ) :
    primitiveCap α β R r hR hr h p T hκ F B η good q ≫
      (push (source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f (((m + 1) + (m + p)) + q) ≫
      absoluteChain (ambient α β) ((m + 1) + (m + p)) q (((m + 1) + (m + p)) + q) rfl (primitive α β r hr h p T hκ) :=
  component_source α β R r hR hr F B η κ ρ _ _ _ _ _ _ _ q

theorem boundaryCap_source (q : ℕ) :
    boundaryCap α β R r hR hr h p T hκ F B η goodδ q ≫
      (push (source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) :=
  component_source α β R r hR hr F B η κ ρ _ _ _ _ _ _ _ q

theorem boundary (q : ℕ) :
    primitiveCap α β R r hR hr h p T hκ F B η good (q + 1) ≫
      (chains (TopCat.of (bounded α β R r hR hr F B))).d (q + 1) q =
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).d
      (((m + 1) + (m + p)) + (q + 1)) (((m + 1) + (m + p)) + q) ≫
        primitiveCap α β R r hR hr h p T hκ F B η good q -
    eqToHom (congrArg (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X
      (show ((m + 1) + (m + p)) + (q + 1) = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
        boundaryCap α β R r hR hr h p T hκ F B η goodδ q :=
  LiftedCapCochainBoundary.boundary (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (chains (TopCat.of (bounded α β R r hR hr F B))) (push (source α β R r hR hr F B))
    (source_mono α β R r hR hr F B) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)
    (primitiveCap α β R r hR hr h p T hκ F B η good) (boundaryCap α β R r hR hr h p T hκ F B η goodδ)
    (primitiveCap_source α β R r hR hr h p T hκ F B η good)
    (boundaryCap_source α β R r hR hr h p T hκ F B η goodδ) q

end
end Finsler.OriginalFirstHalfCupOneBounded
