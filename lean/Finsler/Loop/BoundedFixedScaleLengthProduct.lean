module

public import Finsler.Loop.BoundedSmallJoinComparison

/-! The genuine strict-length product at the original before-threshold
kappa/R. There is no R < product-radius hypothesis. Only the specified
Thom representative is moved through a smaller open neighborhood; the
original normalized cap, rectangles, and uniform filtered join stay fixed. -/

@[expose] public section
namespace Finsler.BoundedFixedScaleLengthProduct

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) {ε : ℝ} (hε : 0 < ε) (R : ℝ) (hR : R ≤ 1 / 2)
  (hRu : R < BoundedCarrierUniformRawJoin.radius α β r hr F hε)
  (B b : ℝ) (hβ : ∀ y, SobolevLength.length F (β y) < b) (hB : 0 < B) (hb : 0 < b)
  (κ : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

include hB hb in
theorem operation_homology (hm : 1 ≤ m) (k : ℕ) :
    ((BoundedCarrierJoinCover.unrefined α β r hr F B κ R hκ hκR).post
      (push (BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu B b hβ))).homology k =
    ((StrictLengthLoopProduct.operation F (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F B) β F B b
        (BoundedKeptProductInputs.length_lt α r hr F B) hβ))).homology k := by
  have hRpos : 0 < R := lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 2) hκ) hκR
  have hκ2 : κ ≤ 2 := by linarith
  let s := min R (StrictLengthProductJoinComparison.radius F B b hB hb hε) / 2
  have hp := StrictLengthProductJoinComparison.radius_pos F B b hB hb hε
  have hs : 0 < s := div_pos (lt_min hRpos hp) (by norm_num)
  have hsR : s ≤ R := by dsimp [s]; linarith [min_le_left R (StrictLengthProductJoinComparison.radius F B b hB hb hε)]
  have hsP : s < StrictLengthProductJoinComparison.radius F B b hB hb hε := by
    dsimp [s]
    linarith [min_le_right R (StrictLengthProductJoinComparison.radius F B b hB hb hε)]
  have hc := BoundedSpecifiedCapShrink.homology_eq α β r hr F B κ R hκ hκR s hs hsR hm hκ2 k
  have ht := BoundedSmallJoinComparison.thom_shrink α β r hr F hε B b hβ hB hb s hs hsP k
  have hj := BoundedSmallJoinComparison.raw_square α β r hr F hε R hR hRu B b hβ hB hb s hsR hsP
  rw [DegreeLoweringHomology.Map.post_homology, hc, DegreeLoweringHomology.Map.post_homology,
    Category.assoc, ← HomologicalComplex.homologyMap_comp, ← push_comp, hj, push_comp,
    HomologicalComplex.homologyMap_comp, ← Category.assoc, ← ht,
    StrictLengthProductFamilies.operation_factor (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m) k,
    StrictLengthProductFamilies.geometricOperation, DegreeLoweringHomology.Map.post_homology]

include hB hb in
theorem product_factor (hm : 1 ≤ m) (i j k : ℕ) (h : i + j = (m + 1) + k)
    (x : PoolCap.homology (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) i)
    (y : PoolCap.homology (TopCat.of Q) j) :
    StrictLengthLoopProduct.product F (dim_pos m) hε i j k h
      ((PoolCap.push (FirstInputSelfCutBoundedSpace.retained α r hr F B) i).hom x)
      ((PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j).hom y) =
    (((BoundedCarrierJoinCover.unrefined α β r hr F B κ R hκ hκR).post
      (push (BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu B b hβ))).homology k).hom
      (FilteredBilinearLoopProduct.cross (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B))
        (TopCat.of Q) i j ((m + 1) + k) h x y) := by
  rw [← BoundedKeptProductInputs.short_input α r hr F B,
    operation_homology α β r hr F hε R hR hRu B b hβ hB hb κ hκ hκR hm k,
    StrictLengthProductFamilies.operation_factor (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m) k]
  exact StrictLengthProductFamilies.product_factor (BoundedKeptProductInputs.kept α r hr F B) β F B b
    (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m) i j k h x y

include hB hb in
theorem tensor_homology_factor (hm : 1 ≤ m) (k : ℕ) :
    ((BoundedCarrierExternalJoin.operation α β r hr F B κ R hκ hκR).post
      (push (BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu B b hβ))).homology k =
    HomologicalComplex.homologyMap
      (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
        (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) ≫
        inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
          (BoundedCarrierJoinCap.rectangles α β r hr F B κ)) ((m + 1) + k) ≫
    HomologicalComplex.homologyMap (push (StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ)) ((m + 1) + k) ≫
    (StrictLengthLoopProduct.operation F (dim_pos m) hε).homology k := by
  have he : ((BoundedCarrierExternalJoin.operation α β r hr F B κ R hκ hκR).post
      (push (BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu B b hβ))).homology k =
    (((BoundedCarrierJoinCover.unrefined α β r hr F B κ R hκ hκR).post
      (push (BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu B b hβ))).pre
      (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
        (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) ≫
        inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
          (BoundedCarrierJoinCap.rectangles α β r hr F B κ))).homology k := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro q
    dsimp only [DegreeLoweringHomology.Map.pre, DegreeLoweringHomology.Map.post, BoundedCarrierExternalJoin.operation]
    rw [HomologicalComplex.comp_f]
    have hs := BoundedCarrierJoinCover.on_small α β r hr F B κ R hκ hκR q
    have ht := congrArg (fun z =>
      (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
        (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ)
        (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f ((m + 1) + q) ≫ z ≫
          (push (BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu B b hβ)).f q) hs
    simpa only [Category.assoc] using ht.symm
  rw [he, DegreeLoweringHomology.Map.pre_homology,
    operation_homology α β r hr F hε R hR hRu B b hβ hB hb κ hκ hκR hm k,
    DegreeLoweringHomology.Map.pre_homology]

end
end Finsler.BoundedFixedScaleLengthProduct
