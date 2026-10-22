module

public import Finsler.Loop.FirstInputSelfCutExternalJoin
public import Finsler.Loop.FirstInputSelfCutFactorwiseRefinement
public import Finsler.Loop.CapComponentRegradedSource
public import Finsler.Loop.OriginalFirstHalfFactorwiseNormalizedTime
public import Finsler.Loop.OriginalFirstHalfCutOutputJoinBounded

/-! On actual common factorwise carriers the real single-input cut,
external beta and localized output join equal the actual bounded
normalized cup component. Only chain source monicity is cancelled. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedFactorization

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {κ δ ρ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R)
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (B η σ : ℝ)
  (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
  (index : (ClosedInterval × P) × Q → Option (Option (FirstInputRotationCochains.space α β R r)))
  (hindex : ∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
    (SmallRectangleShuffle.rectangles (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) c)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c)))
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (otherIndex : Q → Q)
  (hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
    OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c))

def firstMap := SmallRefinementComparison.refinement (X := ambient α)
  (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst

def otherMap := SmallRefinementComparison.refinement (X := TopCat.of Q)
  (OriginalFirstHalfFactorwiseCover.other σ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) otherIndex hother

def inputComponent (i j : ℕ) :=
  (firstMap α r hr σ firstIndex hfirst).f (((m + 1) + p) + i) ⊗ₘ
    (otherMap β σ otherIndex hother).f j

def ambientInput (i j : ℕ) :=
  ((inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + 1) + p) + i) ⊗ₘ
    (inclusion (TopCat.of Q) (OriginalFirstHalfFactorwiseCover.other σ)).f j) ≫
    SingularChainCross.component (ambient α) (TopCat.of Q) (((m + 1) + p) + i) j ≫
    (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f ((((m + 1) + p) + i) + j)

theorem input_inclusion (i j : ℕ) :
    inputComponent α β r hr p σ firstIndex hfirst otherIndex hother i j ≫
      ((inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + i) ⊗ₘ
        (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f j) =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + 1) + p) + i) ⊗ₘ
      (inclusion (TopCat.of Q) (OriginalFirstHalfFactorwiseCover.other σ)).f j := by
  have hx := congrArg (fun f => f.f (((m + 1) + p) + i))
    (SmallRefinementComparison.refinement_inclusion (X := ambient α)
      (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst)
  have hy := congrArg (fun f => f.f j)
    (SmallRefinementComparison.refinement_inclusion (X := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.other σ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) otherIndex hother)
  simp only [HomologicalComplex.comp_f] at hx hy
  dsimp only [inputComponent, firstMap, otherMap]
  rw [tensorHom_comp_tensorHom, hx, hy]

def geometric (i j q : ℕ) (hij : i + j = (m + 1) + q) :=
  inputComponent α β r hr p σ firstIndex hfirst otherIndex hother i j ≫
    FirstInputSelfCutExternalJoin.component α β R r hr hκ hκR h p T hT i j q hij

def bounded (i j q : ℕ) (hij : i + j = (m + 1) + q) :=
  SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) (((m + 1) + p) + i) j ≫
  (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f ((((m + 1) + p) + i) + j) ≫
  eqToHom (congrArg (small (OriginalFirstHalfCupOneCochains.ambient α β)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X
    (show (((m + 1) + p) + i) + j = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
  OriginalFirstHalfNormalizationBounded.normalizedCap α β R r hR hr h p T hκ F B η goodN q

theorem geometric_source (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    geometric α β R r hr hκ hκR h p T hT σ firstIndex hfirst otherIndex hother i j q hij ≫
      (push (OriginalFirstHalfCutThenJoinCap.source α β R r hr)).f q =
    ambientInput α β p σ i j ≫ absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β)
      (((m + 1) + (m + p)) + 1) q ((((m + 1) + p) + i) + j) (by omega)
      (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) := by
  dsimp only [geometric]
  rw [Category.assoc, FirstInputSelfCutExternalJoin.component_source]
  have hh := congrArg (fun k => k ≫
    SingularChainCross.component (ambient α) (TopCat.of Q) (((m + 1) + p) + i) j ≫
    (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f ((((m + 1) + p) + i) + j) ≫
    absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β) (((m + 1) + (m + p)) + 1) q
      ((((m + 1) + p) + i) + j) (by omega) (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ))
    (input_inclusion α β r hr p σ firstIndex hfirst otherIndex hother i j)
  simpa only [ambientInput, Category.assoc] using hh

theorem mapped_input_source (i j : ℕ) :
    SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) (((m + 1) + p) + i) j ≫
    (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f ((((m + 1) + p) + i) + j) ≫
    (inclusion (OriginalFirstHalfCupOneCochains.ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f
      ((((m + 1) + p) + i) + j) = ambientInput α β p σ i j := by
  have hm := SmallRetractionComparison.map_inclusion
    (X := ambient α ⊗ TopCat.of Q) (Y := OriginalFirstHalfCupOneCochains.ambient α β)
    (SmallRectangleShuffle.rectangles (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ))
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex
  have hh := congrArg (fun f => SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    (((m + 1) + p) + i) j ≫ f.f ((((m + 1) + p) + i) + j)) hm
  simp only [HomologicalComplex.comp_f] at hh
  rw [← Category.assoc _ _ ((push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f _),
    SmallNormalizedCapShuffle.component_inclusion] at hh
  simpa only [ambientInput, FirstFactorMappedRectangles.targetMap, Category.assoc] using hh

theorem bounded_source (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    bounded α β R r hR hr hκ h p T F B η σ goodN index hindex i j q hij ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
    ambientInput α β p σ i j ≫ absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β)
      (((m + 1) + (m + p)) + 1) q ((((m + 1) + p) + i) + j) (by omega)
      (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) := by
  have hs := CapComponentRegradedSource.source
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
    (((m + 1) + (m + p)) + 1) q ((((m + 1) + p) + i) + j) (by omega)
    (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ)
    (SmallNormalizedCapShuffle.component (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) (((m + 1) + p) + i) j ≫
      (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
        (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
        (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
        (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f ((((m + 1) + p) + i) + j))
    (OriginalFirstHalfNormalizationBounded.normalizedCap α β R r hR hr h p T hκ F B η goodN q)
    (OriginalFirstHalfNormalizationBounded.normalizedCap_source α β R r hR hr h p T hκ F B η goodN q)
  simp only [Category.assoc] at hs
  rw [show bounded α β R r hR hr hκ h p T F B η σ goodN index hindex i j q hij ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q = _ from hs]
  have hh := congrArg (fun k => k ≫ absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β)
    (((m + 1) + (m + p)) + 1) q ((((m + 1) + p) + i) + j) (by omega)
    (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ))
    (mapped_input_source α β R r p η σ index hindex i j)
  simpa only [Category.assoc] using hh

theorem component_eq (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    geometric α β R r hr hκ hκR h p T hT σ firstIndex hfirst otherIndex hother i j q hij =
    bounded α β R r hR hr hκ h p T F B η σ goodN index hindex i j q hij ≫
      (push (OriginalFirstHalfCutOutputJoinBounded.toNear α β R r hR hr F B)).f q := by
  haveI := OriginalFirstHalfCutThenJoinCap.source_mono α β R r hr q
  apply (cancel_mono ((push (OriginalFirstHalfCutThenJoinCap.source α β R r hr)).f q)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← push_comp,
    OriginalFirstHalfCutOutputJoinBounded.source_square,
    geometric_source, bounded_source]

end
end Finsler.FirstInputSelfCutBoundedFactorization
