module

public import Finsler.Loop.OriginalTimeCanonicalProduct
public import Finsler.Loop.SingleCutCanonicalAnyRadius
public import Finsler.Loop.OriginalTimeCrossNonpositive

/-! The actual original retained homogeneous first-half time is the
specified product of actual canonical D_T(first) and the actual beta
input, for all real individual thresholds. Genuine native zero branches
supply the nonpositive cases. The original scales remain unchanged, with any rho<r and no rho=S/2 condition. -/

@[expose] public section
namespace Finsler.OriginalTimeCanonicalAnyRadius

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover Finsler.StrictLengthEnergyBridge
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {κ δ ρ : ℝ} (hκ : 0 < κ) (h2κR : 2 * κ ≤ R) (hκR : κ < R)
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a b A L η σ : ℝ) (hε : 0 < ε) (hη : 0 < η) (hσ : 0 < σ) (hρr : ρ < r)
  (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η (((m + 1) + (m + p)) + 1)
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

  (hRu : R < BoundedCarrierUniformRawJoin.radius α β r hr F hε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)
  (hab : a + b < A) (hβ : ∀ y, SobolevLength.length F (β y) < b)

include h2κR otherIndex hother hRu hradius hsmall firstIndex hfirst hA in
theorem homology_factor (hm : 1 ≤ m) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
      (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
        hη hσ hρr goodN index hindex).homology k =
    (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshortT).pre
      (push (CompactInputShortMaps.family α F a hA))).homology i ⊗ₘ
      PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j) ≫
    FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij ≫
      (StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k := by
  by_cases hB : 0 < a - L + 3 * ε
  · by_cases hb : 0 < b
    · rw [OriginalTimeCanonicalProduct.retained_product α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
        hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ
        hm hB hb i j k hij,
        SingleCutCanonicalAnyRadius.retained_canonical_DT α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
          firstIndex hfirst hshortT hA hρr hm true i]
    · rw [OriginalTimeCrossNonpositive.beta_homology α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
        hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ
        (le_of_not_gt hb) i j k hij,
        StrictLengthProductBudget.nonpos_homology F (L := L) hab hε (dim_pos m) (fun hpos => hb hpos.2) k]
      simp only [comp_zero]
  · rw [OriginalTimeCrossNonpositive.first_homology α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
      hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ
      (le_of_not_gt hB) i j k hij,
      StrictLengthProductBudget.nonpos_homology F (L := L) hab hε (dim_pos m) (fun hpos => hB hpos.1) k]
    simp only [comp_zero]

include h2κR otherIndex hother hRu hradius hsmall firstIndex hfirst in
theorem product_value (hm : 1 ≤ m) (i j k : ℕ) (hij : i + j = (m + 1) + k)
    (x : PoolCap.homology (TopCat.of P) ((m + p) + i)) (y : PoolCap.homology (TopCat.of Q) j) :
    ((BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
      hη hσ hρr goodN index hindex).homology k).hom
      ((homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j
        (((m + 1) + (m + p)) + k) (by omega)).hom (x ⊗ₜ[ZMod 2] y)) =
    StrictLengthProductBudget.product F (L := L) hab hε (dim_pos m) i j k hij
      ((((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshortT).pre
        (push (CompactInputShortMaps.family α F a hA))).homology i).hom x)
      ((PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j).hom y) := by
  rw [StrictLengthProductBudget.chain_apply, FilteredBilinearLoopProduct.cross_apply]
  have he := ConcreteCategory.congr_hom
    (homology_factor α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ hε hη hσ hρr
      goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ hm i j k hij)
    (x ⊗ₜ[ZMod 2] y)
  change _ = ((StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k).hom
    ((FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij).hom
      (((((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshortT).pre
        (push (CompactInputShortMaps.family α F a hA))).homology i) ⊗ₘ
          PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j) (x ⊗ₜ[ZMod 2] y))) at he
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul] at he
  exact he

end
end Finsler.OriginalTimeCanonicalAnyRadius
