module

public import Finsler.Loop.FirstInputSelfCutTimeFactorization
public import Finsler.Loop.OriginalFirstHalfNormalizedLowDegree

/-! Actual bounded cap and all-input time vanishing in the remaining
low first-input degrees, using the normalized original gamma. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutLowDegreeTime

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {κ δ ρ : ℝ} (hκ : 0 < κ) (hκR : κ < R)
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (B η σ : ℝ) (hη : 0 < η) (hσ : 0 < σ) (hρr : ρ < r)
  (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
  (index : (ClosedInterval × P) × Q → Option (Option (FirstInputRotationCochains.space α β R r)))
  (hindex : ∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
    (SmallRectangleShuffle.rectangles (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) c)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c)))

def ambientInput (l j : ℕ) :=
  ((inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f l ⊗ₘ
    (inclusion (TopCat.of Q) (OriginalFirstHalfFactorwiseCover.other σ)).f j) ≫
    SingularChainCross.component (ambient α) (TopCat.of Q) l j ≫
    (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f (l + j)

def bounded (l j q : ℕ) (hN : l + j = (((m + 1) + (m + p)) + 1) + q) :=
  SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) l j ≫
  (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f (l + j) ≫
  eqToHom (congrArg (small (OriginalFirstHalfCupOneCochains.ambient α β)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X
    (show l + j = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
  OriginalFirstHalfNormalizationBounded.normalizedCap α β R r hR hr h p T hκ F B η goodN q

theorem mapped_input_source (l j : ℕ) :
    SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) l j ≫
    (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f (l + j) ≫
    (inclusion (OriginalFirstHalfCupOneCochains.ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f
      (l + j) = ambientInput α β σ l j := by
  have hm := SmallRetractionComparison.map_inclusion
    (X := ambient α ⊗ TopCat.of Q) (Y := OriginalFirstHalfCupOneCochains.ambient α β)
    (SmallRectangleShuffle.rectangles (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ))
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex
  have hh := congrArg (fun f => SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    l j ≫ f.f (l + j)) hm
  simp only [HomologicalComplex.comp_f] at hh
  rw [← Category.assoc _ _ ((push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f _),
    SmallNormalizedCapShuffle.component_inclusion] at hh
  simpa only [ambientInput, FirstFactorMappedRectangles.targetMap, Category.assoc] using hh

theorem bounded_source (l j q : ℕ) (hN : l + j = (((m + 1) + (m + p)) + 1) + q) :
    bounded α β R r hR hr hκ h p T F B η σ goodN index hindex l j q hN ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
    ambientInput α β σ l j ≫ absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β)
      (((m + 1) + (m + p)) + 1) q (l + j) (by omega)
      (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) := by
  have hs := CapComponentRegradedSource.source
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
    (((m + 1) + (m + p)) + 1) q (l + j) (by omega)
    (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ)
    (SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) l j ≫
      (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
        (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
        (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
        (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f (l + j))
    (OriginalFirstHalfNormalizationBounded.normalizedCap α β R r hR hr h p T hκ F B η goodN q)
    (OriginalFirstHalfNormalizationBounded.normalizedCap_source α β R r hR hr h p T hκ F B η goodN q)
  simp only [Category.assoc] at hs
  rw [show bounded α β R r hR hr hκ h p T F B η σ goodN index hindex l j q hN ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q = _ from hs]
  have hh := congrArg (fun k => k ≫ absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β)
    (((m + 1) + (m + p)) + 1) q (l + j) (by omega)
    (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ))
    (mapped_input_source α β R r η σ index hindex l j)
  simpa only [Category.assoc] using hh

theorem bounded_zero (l j q : ℕ) (hN : l + j = (((m + 1) + (m + p)) + 1) + q)
    (hl : l < (m + 1) + p) :
    bounded α β R r hR hr hκ h p T F B η σ goodN index hindex l j q hN = 0 := by
  haveI := OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B q
  apply (cancel_mono ((push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q)).mp
  rw [zero_comp, bounded_source]
  simp only [ambientInput, Category.assoc]
  rw [OriginalFirstHalfNormalizedLowDegree.cup_zero α β r hr h p T hκ l j q hN.symm hl, comp_zero]

def prefixComponent (l j : ℕ) :=
  FirstFactorSectionedPrismSummand.firstPrefix (X := TopCat.of P)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
    (OriginalFirstHalfFactorwiseCover.first_univ hσ) l ⊗ₘ
    (TauCeti.smallSingularRetraction (X := TopCat.of Q) coeff (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)).f j

theorem bounded_time_on_summand (l j q : ℕ) (hN : l + j = ((m + 1) + (m + p)) + q) :
    ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) l j
      (((m + 1) + (m + p)) + q) hN ≫
      (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F B η hη hρr
        goodN hT σ hσ index hindex).component q =
    prefixComponent (P := P) (Q := Q) σ hσ l j ≫
      bounded α β R r hR hr hκ h p T F B η σ goodN index hindex (l + 1) j q (by omega) := by
  have hs := FirstFactorSectionedSmallCross.on_summand (X := TopCat.of P) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)
    l j (((m + 1) + (m + p)) + q) hN
  have ht := congrArg (fun f => f ≫
    (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f
        (((m + 1) + (m + p)) + q + 1) ≫
    OriginalFirstHalfFactorwiseNormalizedTime.smallCap α β R r hR hr h p T hκ F B η goodN hT q) hs
  rw [OriginalFirstHalfFactorwiseNormalizedTime.component_normal]
  simp only [FirstFactorSectionedPrismSummand.inputRetraction, Category.assoc] at ht
  rw [ht]
  simp only [prefixComponent, bounded, OriginalFirstHalfFactorwiseNormalizedTime.smallCap,
    SingleCapTimeRefinement.aligned_normal, Category.assoc]
  have hm := LocalizedCapCupComponentSource.transport_f
    (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex)
    ((l + 1) + j) (((m + 1) + (m + p)) + q + 1) (by omega)
  rw [← Category.assoc (eqToHom _), hm]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _), eqToHom_trans]
  rfl

theorem time_zero (l j q : ℕ) (hN : l + j = ((m + 1) + (m + p)) + q) (hl : l < m + p) :
    ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) l j
      (((m + 1) + (m + p)) + q) hN ≫
      (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F B η hη hρr
        goodN hT σ hσ index hindex).component q = 0 := by
  rw [bounded_time_on_summand, bounded_zero α β R r hR hr hκ h p T F B η σ goodN index hindex
    (l + 1) j q (by omega) (by omega), comp_zero]

end
end Finsler.FirstInputSelfCutLowDegreeTime
