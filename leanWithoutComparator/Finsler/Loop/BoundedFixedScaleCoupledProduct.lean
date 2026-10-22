module

public import Finsler.Loop.BoundedFixedScaleLengthProduct
public import Finsler.Loop.BoundedCarrierFilteredOutput

/-! The original fixed kappa/R cap and whole closed small tensor join
realize the strict-length product in the literal coupled short target.
No later product-radius condition remains. -/

@[expose] public section
namespace Finsler.BoundedFixedScaleCoupledProduct

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) {ε : ℝ} (hε : 0 < ε) (R : ℝ) (hR : R ≤ 1 / 2)
  (hRu : R < BoundedCarrierUniformRawJoin.radius α β r hr F hε)
  {a b A L : ℝ} (hab : a + b < A) (hβ : ∀ y, SobolevLength.length F (β y) < b)
  (hB : 0 < a - L + 3 * ε) (hb : 0 < b)
  (κ : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

def operation := (BoundedCarrierJoinCover.unrefined α β r hr F (a - L + 3 * ε) κ R hκ hκR).post
  (push (BoundedCarrierFilteredOutput.joinMap α β r hr F hε R hR hRu (L := L) hab hβ))

include hB hb in
theorem operation_homology (hm : 1 ≤ m) (k : ℕ) :
    (operation α β r hr F hε R hR hRu (L := L) hab hβ κ hκ hκR).homology k =
    ((StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).pre
      (push (StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F (a - L + 3 * ε)) β F
        (a - L + 3 * ε) b (BoundedKeptProductInputs.length_lt α r hr F (a - L + 3 * ε)) hβ))).homology k := by
  have he := BoundedFixedScaleLengthProduct.operation_homology α β r hr F hε R hR hRu (a - L + 3 * ε) b hβ hB hb κ hκ hκR hm k
  have ht := congrArg (fun z => z ≫ HomologicalComplex.homologyMap (push (StrictLengthProductBudget.outputInclusion F (L := L) hab hε)) k) he
  simpa only [operation, BoundedCarrierFilteredOutput.joinMap, DegreeLoweringHomology.Map.post_homology,
    push_comp, HomologicalComplex.homologyMap_comp, StrictLengthProductBudget.operation,
    DegreeLoweringHomology.Map.pre_homology, Category.assoc] using ht

include hB hb in
theorem product_factor (hm : 1 ≤ m) (i j k : ℕ) (h : i + j = (m + 1) + k)
    (x : PoolCap.homology (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε))) i)
    (y : PoolCap.homology (TopCat.of Q) j) :
    StrictLengthProductBudget.product F (L := L) hab hε (dim_pos m) i j k h
      ((PoolCap.push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε)) i).hom x)
      ((PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j).hom y) =
    ((operation α β r hr F hε R hR hRu (L := L) hab hβ κ hκ hκR).homology k).hom
      (FilteredBilinearLoopProduct.cross (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (TopCat.of Q) i j ((m + 1) + k) h x y) := by
  rw [← BoundedKeptProductInputs.short_input α r hr F (a - L + 3 * ε), StrictLengthProductBudget.chain_apply,
    CrossProjectionZero.cross_naturality_apply]
  have he := ConcreteCategory.congr_hom (operation_homology α β r hr F hε R hR hRu (L := L) hab hβ hB hb κ hκ hκR hm k)
    (FilteredBilinearLoopProduct.cross (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (TopCat.of Q) i j ((m + 1) + k) h x y)
  rw [DegreeLoweringHomology.Map.pre_homology] at he
  exact he.symm

include hB hb in
theorem tensor_homology_factor (hm : 1 ≤ m) (k : ℕ) :
    ((BoundedCarrierExternalJoin.operation α β r hr F (a - L + 3 * ε) κ R hκ hκR).post
      (push (BoundedCarrierFilteredOutput.joinMap α β r hr F hε R hR hRu (L := L) hab hβ))).homology k =
    HomologicalComplex.homologyMap
      (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε))) (Y := TopCat.of Q)
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) ≫
        inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε) × Q))
          (BoundedCarrierJoinCap.rectangles α β r hr F (a - L + 3 * ε) κ)) ((m + 1) + k) ≫
    HomologicalComplex.homologyMap (push (StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F (a - L + 3 * ε)) β F
      (a - L + 3 * ε) b (BoundedKeptProductInputs.length_lt α r hr F (a - L + 3 * ε)) hβ)) ((m + 1) + k) ≫
    (StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k := by
  have he := BoundedFixedScaleLengthProduct.tensor_homology_factor α β r hr F hε R hR hRu (a - L + 3 * ε) b hβ hB hb κ hκ hκR hm k
  have ht := congrArg (fun z => z ≫ HomologicalComplex.homologyMap (push (StrictLengthProductBudget.outputInclusion F (L := L) hab hε)) k) he
  simpa only [BoundedCarrierFilteredOutput.joinMap, DegreeLoweringHomology.Map.post_homology,
    push_comp, HomologicalComplex.homologyMap_comp, StrictLengthProductBudget.operation, Category.assoc] using ht

end
end Finsler.BoundedFixedScaleCoupledProduct
