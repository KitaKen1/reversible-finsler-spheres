module

public import Finsler.Loop.FirstFactorSectionedSmallCross
public import Finsler.Loop.FirstInputSelfCutTimePrefix

/-! Actual single-input normalized cut-time followed by external beta and
localized output join. The native bounded time component factors this way
on every compatible homogeneous input, including output degree zero. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutTimeFactorization

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
  (hR : R ≤ 1 / 2) (hr : r < 1) {κ δ ρ : ℝ} (hκ : 0 < κ) (h2κR : 2 * κ ≤ R) (hκR : κ < R)
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
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (otherIndex : Q → Q)
  (hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
    OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c))


def otherSection (j : ℕ) :=
  (TauCeti.smallSingularRetraction (X := TopCat.of Q) coeff (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)).f j ≫
  (FirstInputSelfCutBoundedFactorization.otherMap β σ otherIndex hother).f j

def prefixComponent (i j : ℕ) :=
  FirstInputSelfCutTimePrefix.timePrefix α p σ hσ i ⊗ₘ
    (TauCeti.smallSingularRetraction (X := TopCat.of Q) coeff (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)).f j

def geometric (i j q : ℕ) (hij : i + j = (m + 1) + q) :=
  ((FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst true).component i ⊗ₘ
    otherSection β σ hσ otherIndex hother j) ≫
  SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
    (carrier α r hr κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j ≫
  eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
    (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).X hij) ≫
  (CompactJoinCapLocalization.localized (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (by omega) hκ h2κR).component q

theorem geometric_prefix (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    geometric α β R r hr hκ h2κR h p T hT σ hσ firstIndex hfirst otherIndex hother i j q hij =
    prefixComponent (Q := Q) α p σ hσ i j ≫
      FirstInputSelfCutBoundedFactorization.geometric α β R r hr hκ h2κR h p T hT σ
        firstIndex hfirst otherIndex hother i j q hij := by
  simp only [geometric, FirstInputSelfCutTimePrefix.normalized_component, otherSection, prefixComponent,
    FirstInputSelfCutBoundedFactorization.geometric, FirstInputSelfCutBoundedFactorization.inputComponent,
    FirstInputSelfCutExternalJoin.component, FirstInputSelfCutExternalCap.component, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.assoc]

theorem bounded_on_summand (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j
      (((m + 1) + (m + p)) + q) (by omega) ≫
      (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F B η hη hρr
        goodN hT σ hσ index hindex).component q =
    prefixComponent (Q := Q) α p σ hσ i j ≫
      FirstInputSelfCutBoundedFactorization.bounded α β R r hR hr hκ h p T F B η σ goodN index hindex i j q hij := by
  have hs := FirstFactorSectionedSmallCross.on_summand_regraded (X := TopCat.of P) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)
    ((m + p) + i) j (((m + 1) + (m + p)) + q) (((m + 1) + p) + i) (by omega) (by omega)
  have ht := congrArg (fun f => f ≫
    (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f
        (((m + 1) + (m + p)) + q + 1) ≫
    OriginalFirstHalfFactorwiseNormalizedTime.smallCap α β R r hR hr h p T hκ F B η goodN hT q) hs
  rw [OriginalFirstHalfFactorwiseNormalizedTime.component_normal]
  change _ = _ at ht
  simp only [FirstFactorSectionedPrismSummand.inputRetraction, Category.assoc] at ht
  rw [ht]
  simp only [FirstFactorSectionedSmallCross.timePrefix, FirstInputSelfCutTimePrefix.timePrefix, prefixComponent,
    FirstInputSelfCutBoundedFactorization.bounded, OriginalFirstHalfFactorwiseNormalizedTime.smallCap,
    SingleCapTimeRefinement.aligned_normal, Category.assoc]
  have hm := LocalizedCapCupComponentSource.transport_f
    (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex)
    ((((m + 1) + p) + i) + j) (((m + 1) + (m + p)) + q + 1) (by omega)
  rw [← Category.assoc (eqToHom _), hm]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _), eqToHom_trans]
  rfl

theorem component_eq (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    geometric α β R r hr hκ h2κR h p T hT σ hσ firstIndex hfirst otherIndex hother i j q hij =
    ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j
      (((m + 1) + (m + p)) + q) (by omega) ≫
      (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F B η hη hρr
        goodN hT σ hσ index hindex).component q ≫
      (push (OriginalFirstHalfCutOutputJoinBounded.toNear α β R r hR hr F B)).f q := by
  rw [geometric_prefix, ← Category.assoc, bounded_on_summand,
    Category.assoc, ← FirstInputSelfCutBoundedFactorization.component_eq]

end
end Finsler.FirstInputSelfCutTimeFactorization
