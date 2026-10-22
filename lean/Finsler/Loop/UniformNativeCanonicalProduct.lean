module

public import Finsler.Loop.OriginalTimeCanonicalAnyRadius
public import Finsler.Loop.FirstInputSelfCutUniformIndividualBoundedTime

/-! A genuine before-tested uniform package identifies the original
geometric first-half cut-then-join time with product(D_T(first),beta),
for all later real individual thresholds. All omitted low first-input
degrees vanish. The same original scales and geometric operation are used. No canonical half-radius equality is required, so native-compatible small rho is allowed. -/

@[expose] public section
namespace Finsler.UniformNativeCanonicalProduct

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge
open Finsler.OriginalFirstHalfJointSupportedCap Finsler.OriginalFirstHalfCupOrderCochains
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε t : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r < 1)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (ht : 0 < t)
    (hradius : r < SelfCutLengthControl.radius F hε)
    (hm : 1 ≤ m) :
    ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < u →
      ∃ η : ℝ, ∃ hη : 0 < η, η ≤ t ∧ ∀ (κ : ℝ) (hκ : 0 < κ) (h2κR : 2 * κ ≤ R),
      ∃ hκR : κ < R, ∃ σ : ℝ, ∃ hσ : 0 < σ, σ ≤ t ∧
      ∃ index : (ClosedInterval × P) × Q → Option (Option (FirstInputRotationCochains.space α β R r)),
      ∃ hindex : ∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
        (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × P)) (Y := TopCat.of Q)
          (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) c)
        (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c)),
      ∃ firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r),
      ∃ hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ FirstInputSelfCutCover.cover α r hr κ ρ (firstIndex c),
      ∃ otherIndex : Q → Q,
      ∃ hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
        OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c),
      ∃ hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ,
      ∀ (p : ℕ) (L a b A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
        (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
        (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (SelfCutOscillation.short F L)) p T = 0)
        (hA : ∀ x, SobolevLength.length F (α x) < a)
        (hβ : ∀ y, SobolevLength.length F (β y) < b) (hab : a + b < A),
        ∃ (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          (((m + 1) + (m + p)) + 1) (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
          (goodOld : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v)),
        ∀ k,
          (∀ (i j : ℕ) (hij : i + j = (m + 1) + k),
            FilteredBilinearLoopProduct.crossMap (TopCat.of P) (TopCat.of Q) ((m + p) + i) j
              (((m + 1) + (m + p)) + k) (by omega) ≫
              (OriginalFirstHalfCutThenJoinTime.operation α β R r η hR hr hκ hκR hη h hρr p T F
                (A - L + 5 * ε) goodOld hT).homology k =
            (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
              (push (CompactInputShortMaps.family α F a hA))).homology i ⊗ₘ
              PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j) ≫
            FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij ≫
              (StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k) ∧
          ∀ (l j : ℕ) (hN : l + j = ((m + 1) + (m + p)) + k), l < m + p →
            FilteredBilinearLoopProduct.crossMap (TopCat.of P) (TopCat.of Q) l j
              (((m + 1) + (m + p)) + k) hN ≫
              (OriginalFirstHalfCutThenJoinTime.operation α β R r η hR hr hκ hκR hη h hρr p T F
                (A - L + 5 * ε) goodOld hT).homology k = 0 := by
  obtain ⟨u, hu, hu1, hscale⟩ := FirstInputSelfCutUniformIndividualBoundedTime.exists_uniform
    α β h hρr hr F hε ht hradius
  let v := BoundedCarrierUniformRawJoin.radius α β r hr F hε
  have hv : 0 < v := BoundedCarrierUniformRawJoin.radius_pos α β r hr F hε
  refine ⟨min u v, lt_min hu hv, (min_le_left u v).trans hu1, ?_⟩
  intro R hR hRu
  have hRuOld : R < u := hRu.trans_le (min_le_left u v)
  have hRuRaw : R < BoundedCarrierUniformRawJoin.radius α β r hr F hε := hRu.trans_le (min_le_right u v)
  obtain ⟨η, hη, hηt, hdata⟩ := hscale R hR hRuOld
  refine ⟨η, hη, hηt, ?_⟩
  intro κ hκ h2κR
  obtain ⟨hκR, σ, hσ, hσt, index, hindex, firstIndex, hfirst, otherIndex, hother, hsmall, htested⟩ := hdata κ hκ h2κR
  refine ⟨hκR, σ, hσ, hσt, index, hindex, firstIndex, hfirst, otherIndex, hother, hsmall, ?_⟩
  intro p L a b A T hT hshort hA hβ hab
  have hpair : ∀ x y, SobolevLength.length F (α x) + SobolevLength.length F (β y) < A := by
    intro x y
    exact (add_lt_add (hA x) (hβ y)).trans hab
  obtain ⟨goodχ, goodδ, goodN, goodOld, hcmp⟩ := htested p L A T hT hshort hpair
  refine ⟨goodN, goodOld, ?_⟩
  intro k
  have hmatch := (hcmp k).1
  change (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
      hη hσ hρr goodN index hindex).homology k =
    ((OriginalFirstHalfCutThenJoinTime.operation α β R r η hR hr hκ hκR hη h hρr p T F
      (A - L + 5 * ε) goodOld hT).pre (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))).homology k at hmatch
  constructor
  · intro i j hij
    have hp := OriginalTimeCanonicalAnyRadius.homology_factor α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
      hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRuRaw hradius hsmall hshort hA hab hβ
      hm i j k hij
    rw [hmatch, DegreeLoweringHomology.Map.pre_homology, ← Category.assoc, SmallCrossHomologyBridge.ambient] at hp
    exact hp
  · intro l j hN hl
    have hn := (hcmp k).2.2.1 l j hN hl
    have hz : ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) l j (((m + 1) + (m + p)) + k) hN ≫
        (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
          hη hσ hρr goodN index hindex).component k = 0 := by
      have hh := congrArg (fun z => z ≫ (push (retained α β R r hR hr F (A - L + 5 * ε))).f k) hn
      simpa only [BoundedSelfTimeCrossHomology.retainedOperation, DegreeLoweringHomology.Map.post,
        Category.assoc, zero_comp] using hh
    have hp := DegreeLoweringCrossZero.homology (chains (TopCat.of P)) (chains (TopCat.of Q))
      (chains (lengthSpace F (A - L + 5 * ε))) ((m + 1) + (m + p))
      (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
        hη hσ hρr goodN index hindex) l j k hN hz
    rw [hmatch, DegreeLoweringHomology.Map.pre_homology, ← Category.assoc, SmallCrossHomologyBridge.ambient] at hp
    exact hp

end
end Finsler.UniformNativeCanonicalProduct
