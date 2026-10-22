module

public import Finsler.Loop.OriginalFirstHalfJointSupportedCap
public import Finsler.Loop.OriginalFirstHalfNormalizationCup
public import Finsler.Loop.OriginalFirstHalfNormalizationLocalError
public import Finsler.Loop.OriginalFirstHalfCupOrderBounded
public import Finsler.Loop.LiftedCapCochainBoundary

/-! Actual normalization primitive and coboundary caps, followed by
the normalized cup cap, in the identical bounded original proper domain. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizationBounded

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
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
    (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR))
  (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR)))

def primitiveCap (q : ℕ) :
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X (((m + 1) + (m + p)) + q) ⟶
      (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  component α β R r hR hr F B η κ ρ ((m + 1) + (m + p)) (OriginalFirstHalfNormalizationCup.primitive α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR)
    (OriginalFirstHalfNormalizationCup.primitive_join_far_zero α β r hr h p T hκ) (OriginalFirstHalfNormalizationCup.primitive_cut_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.source_primitive α β r hr h p T hκ R hR) good q

def boundaryCap (q : ℕ) :
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X ((((m + 1) + (m + p)) + 1) + q) ⟶
      (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  component α β R r hR hr F B η κ ρ (((m + 1) + (m + p)) + 1)
    (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (OriginalFirstHalfNormalizationCup.primitive α β r hr h p T hκ))
    (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR))
    (OriginalFirstHalfNormalizationCup.primitive_boundary_join_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.primitive_boundary_cut_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.source_primitive_boundary α β r hr h p T hκ R hR) goodδ q

theorem primitiveCap_source (q : ℕ) :
    primitiveCap α β R r hR hr h p T hκ F B η good q ≫
      (push (source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f (((m + 1) + (m + p)) + q) ≫
      absoluteChain (ambient α β) ((m + 1) + (m + p)) q (((m + 1) + (m + p)) + q) rfl (OriginalFirstHalfNormalizationCup.primitive α β r hr h p T hκ) :=
  component_source α β R r hR hr F B η κ ρ _ _ _ _ _ _ _ q

theorem boundaryCap_source (q : ℕ) :
    boundaryCap α β R r hR hr h p T hκ F B η goodδ q ≫
      (push (source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (OriginalFirstHalfNormalizationCup.primitive α β r hr h p T hκ)) :=
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
    (source_mono α β R r hR hr F B) ((m + 1) + (m + p)) (OriginalFirstHalfNormalizationCup.primitive α β r hr h p T hκ)
    (primitiveCap α β R r hR hr h p T hκ F B η good) (boundaryCap α β R r hR hr h p T hκ F B η goodδ)
    (primitiveCap_source α β R r hR hr h p T hκ F B η good)
    (boundaryCap_source α β R r hR hr h p T hκ F B η goodδ) q

variable (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def normalizedCap (q : ℕ) :
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X ((((m + 1) + (m + p)) + 1) + q) ⟶
      (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  component α β R r hR hr F B η κ ρ (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR)
    (OriginalFirstHalfNormalizationCup.order_join_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.order_cut_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.source_order α β r hr h p T hκ R hR) goodN q

theorem normalizedCap_source (q : ℕ) :
    normalizedCap α β R r hR hr h p T hκ F B η goodN q ≫ (push (source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) :=
  component_source α β R r hR hr F B η κ ρ _ _ _ _ _ _ _ q

include hT in
theorem normalizedCap_comm (q : ℕ) :
    normalizedCap α β R r hR hr h p T hκ F B η goodN (q + 1) ≫
      (chains (TopCat.of (bounded α β R r hR hr F B))).d (q + 1) q =
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).d
      ((((m + 1) + (m + p)) + 1) + (q + 1)) ((((m + 1) + (m + p)) + 1) + q) ≫
      normalizedCap α β R r hR hr h p T hκ F B η goodN q := by
  have hb := LiftedCapCochainBoundary.boundary (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (chains (TopCat.of (bounded α β R r hR hr F B))) (push (source α β R r hR hr F B))
    (source_mono α β R r hR hr F B) (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ)
    (normalizedCap α β R r hR hr h p T hκ F B η goodN) (fun _ => 0)
    (normalizedCap_source α β R r hR hr h p T hκ F B η goodN)
    (fun q => by rw [zero_comp,
      OriginalFirstHalfNormalizationLocalError.order_boundary_small_zero α β R r hR hr h p T hκ η hT q]) q
  simpa only [comp_zero, sub_zero] using hb

def normalizedOperation : DegreeLoweringHomology.Map
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ))
    (chains (TopCat.of (bounded α β R r hR hr F B))) (((m + 1) + (m + p)) + 1) where
  component := normalizedCap α β R r hR hr h p T hκ F B η goodN
  comm := normalizedCap_comm α β R r hR hr h p T hκ F B η goodN hT

include hT in
theorem difference
    (goodOld : ∀ v, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
      (OriginalFirstHalfCupOrderCochains.properOrder α β R r hR hr h p T hκ v)) (q : ℕ) :
    normalizedCap α β R r hR hr h p T hκ F B η goodN q -
      OriginalFirstHalfCupOrderBounded.cap α β R r hR hr h p T hκ F B η goodOld true q =
    boundaryCap α β R r hR hr h p T hκ F B η goodδ q := by
  haveI := source_mono α β R r hR hr F B q
  apply (cancel_mono ((push (source α β R r hR hr F B)).f q)).mp
  rw [Preadditive.sub_comp, normalizedCap_source, OriginalFirstHalfCupOrderBounded.cap_source,
    boundaryCap_source, OriginalFirstHalfNormalizationLocalError.boundary_difference α β R r hR hr h p T hκ η hT q]

end
end Finsler.OriginalFirstHalfNormalizationBounded
