module

public import Finsler.Loop.OriginalFirstHalfCupOrderCochains
public import Finsler.Loop.OriginalFirstHalfJointCochainZero
public import Finsler.Loop.OriginalFirstHalfCupOneBounded
public import Finsler.Loop.OriginalFirstHalfJointError

/-! Both genuine cup-order caps in one actual bounded proper domain.
Their local coboundary vanishes on the real joint cover, so they are
closed operations. Their difference is the actual cup-one boundary cap. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCupOrderBounded

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJointSupportedCap
open Finsler.OriginalFirstHalfCupOrderCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

private theorem coboundary_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (ξ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f (d + 1) (cochainCoboundary (ZMod 2) Y d ξ) =
      cochainCoboundary (ZMod 2) X d (cochainPullback f d ξ) :=
  (ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm d (d + 1)) ξ).symm

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)
  (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (good : ∀ b, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (properOrder α β R r hR hr h p T hκ b))

def cap (b : Bool) (q : ℕ) :
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X ((((m + 1) + (m + p)) + 1) + q) ⟶
      (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  component α β R r hR hr F B η κ ρ (((m + 1) + (m + p)) + 1)
    (originalOrder α β r hr h p T hκ b) (properOrder α β R r hR hr h p T hκ b)
    (original_join_far_zero α β r hr h p T hκ b) (original_cut_far_zero α β r hr h p T hκ b)
    (source_order α β R r hR hr h p T hκ b) (good b) q

theorem cap_source (b : Bool) (q : ℕ) :
    cap α β R r hR hr h p T hκ F B η good b q ≫ (push (source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (originalOrder α β r hr h p T hκ b) :=
  component_source α β R r hR hr F B η κ ρ _ _ _ _ _ _ _ q

include hR in
theorem boundary_small_zero (b : Bool)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f (((((m + 1) + (m + p)) + 1) + 1) + q) ≫
      absoluteChain (ambient α β) ((((m + 1) + (m + p)) + 1) + 1) q (((((m + 1) + (m + p)) + 1) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1)
          (originalOrder α β r hr h p T hκ b)) = 0 := by
  apply OriginalFirstHalfJointCochainZero.small_cap_zero α β R r η κ ρ _ _ _ _ _ q
  · rw [coboundary_pullback, original_join_far_zero]
    exact map_zero _
  · rw [coboundary_pullback, original_cut_far_zero]
    exact map_zero _
  · exact source_coboundary_zero α β R r hR hr h p T hκ b hT

theorem cap_comm (b : Bool)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    cap α β R r hR hr h p T hκ F B η good b (q + 1) ≫
      (chains (TopCat.of (bounded α β R r hR hr F B))).d (q + 1) q =
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).d
      ((((m + 1) + (m + p)) + 1) + (q + 1)) ((((m + 1) + (m + p)) + 1) + q) ≫
        cap α β R r hR hr h p T hκ F B η good b q := by
  have hb := LiftedCapCochainBoundary.boundary (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (chains (TopCat.of (bounded α β R r hR hr F B))) (push (source α β R r hR hr F B))
    (source_mono α β R r hR hr F B) (((m + 1) + (m + p)) + 1)
    (originalOrder α β r hr h p T hκ b) (cap α β R r hR hr h p T hκ F B η good b) (fun _ => 0)
    (cap_source α β R r hR hr h p T hκ F B η good b)
    (fun q => by rw [zero_comp, boundary_small_zero α β R r hR hr h p T hκ η b hT q]) q
  simpa only [comp_zero, sub_zero] using hb

def operation (b : Bool)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    DegreeLoweringHomology.Map (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ))
      (chains (TopCat.of (bounded α β R r hR hr F B))) (((m + 1) + (m + p)) + 1) where
  component := cap α β R r hR hr h p T hκ F B η good b
  comm := cap_comm α β R r hR hr h p T hκ F B η good b hT

theorem difference
    (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
        (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ)))
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    cap α β R r hR hr h p T hκ F B η good false q - cap α β R r hR hr h p T hκ F B η good true q =
      OriginalFirstHalfCupOneBounded.boundaryCap α β R r hR hr h p T hκ F B η goodδ q := by
  haveI := source_mono α β R r hR hr F B q
  apply (cancel_mono ((push (source α β R r hR hr F B)).f q)).mp
  rw [Preadditive.sub_comp, cap_source, cap_source, OriginalFirstHalfCupOneBounded.boundaryCap_source,
    OriginalFirstHalfJointError.commutator_cap α β R r hR hr h p T hT hκ η q]
  rfl

end
end Finsler.OriginalFirstHalfCupOrderBounded
