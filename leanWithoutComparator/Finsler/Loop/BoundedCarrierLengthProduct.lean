module

public import Finsler.Loop.BoundedCarrierCapThomComparison
public import Finsler.Loop.BoundedCarrierExternalJoin

/-! The real closed join on proper-centered bounded-carrier rectangles
induces the genuine strict-length product. The actual small tensor
operation, not only individual product values, has the proved homology
factorization through the real coefficient-multiplied external cross. -/

@[expose] public section
namespace Finsler.BoundedCarrierLengthProduct

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B b : ℝ) (hβ : ∀ y, SobolevLength.length F (β y) < b)
  (hB : 0 < B) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε)
  (κ R : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)
  (hR : R < StrictLengthProductJoinComparison.radius F B b hB hb hε)

def joinMap := CompactLocalizedLengthProduct.joinMap (BoundedKeptProductInputs.kept α r hr F B) β F B b
  (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε R hR

def operation := (BoundedCarrierJoinCover.unrefined α β r hr F B κ R hκ hκR).post
  (push (joinMap α β r hr F B b hβ hB hb hε R hR))

theorem cap_homology (hm : 1 ≤ m) (k : ℕ) :
    (BoundedCarrierJoinCover.unrefined α β r hr F B κ R hκ hκR).homology k ≫
      HomologicalComplex.homologyMap (push (CompactLocalizedLengthProduct.toProductTube
        (BoundedKeptProductInputs.kept α r hr F B) β F B b (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε R hR)) k =
    (StrictLengthProductFamilies.thomOperation (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m)).homology k := by
  rw [← DegreeLoweringHomology.Map.post_homology]
  have he := (BoundedCarrierCapThomComparison.existing_unrefined α β r hr F B κ R
    (StrictLengthProductJoinComparison.radius F B b hB hb hε) hκ hκR hR k).trans
      (BoundedCarrierCapThomComparison.specified_homology α β r hr F B κ R
        (StrictLengthProductJoinComparison.radius F B b hB hb hε) hκ hκR hR hm
        (CompactLocalizedLengthProduct.rho_le_two F B b hB hb hε R hκR hR) k)
  exact he

theorem operation_homology (hm : 1 ≤ m) (k : ℕ) :
    (operation α β r hr F B b hβ hB hb hε κ R hκ hκR hR).homology k =
    ((StrictLengthLoopProduct.operation F (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F B) β F B b
        (BoundedKeptProductInputs.length_lt α r hr F B) hβ))).homology k := by
  rw [operation, DegreeLoweringHomology.Map.post_homology, joinMap, CompactLocalizedLengthProduct.joinMap, push_comp,
    HomologicalComplex.homologyMap_comp, ← Category.assoc, cap_homology α β r hr F B b hβ hB hb hε κ R hκ hκR hR hm k,
    StrictLengthProductFamilies.operation_factor (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m) k,
    StrictLengthProductFamilies.geometricOperation, DegreeLoweringHomology.Map.post_homology]

theorem product_factor (hm : 1 ≤ m) (i j k : ℕ) (h : i + j = (m + 1) + k)
    (x : PoolCap.homology (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) i)
    (y : PoolCap.homology (TopCat.of Q) j) :
    StrictLengthLoopProduct.product F (dim_pos m) hε i j k h
      ((PoolCap.push (FirstInputSelfCutBoundedSpace.retained α r hr F B) i).hom x)
      ((PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j).hom y) =
    ((operation α β r hr F B b hβ hB hb hε κ R hκ hκR hR).homology k).hom
      (FilteredBilinearLoopProduct.cross (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B))
        (TopCat.of Q) i j ((m + 1) + k) h x y) := by
  rw [← BoundedKeptProductInputs.short_input α r hr F B, operation_homology α β r hr F B b hβ hB hb hε κ R hκ hκR hR hm k,
    StrictLengthProductFamilies.operation_factor (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m) k]
  exact StrictLengthProductFamilies.product_factor (BoundedKeptProductInputs.kept α r hr F B) β F B b
    (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m) i j k h x y

theorem tensor_homology_factor (hm : 1 ≤ m) (k : ℕ) :
    ((BoundedCarrierExternalJoin.operation α β r hr F B κ R hκ hκR).post
      (push (joinMap α β r hr F B b hβ hB hb hε R hR))).homology k =
    HomologicalComplex.homologyMap
      (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
        (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) ≫
        inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
          (BoundedCarrierJoinCap.rectangles α β r hr F B κ)) ((m + 1) + k) ≫
    HomologicalComplex.homologyMap (push (StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ)) ((m + 1) + k) ≫
    (StrictLengthLoopProduct.operation F (dim_pos m) hε).homology k := by
  have he : ((BoundedCarrierExternalJoin.operation α β r hr F B κ R hκ hκR).post
      (push (joinMap α β r hr F B b hβ hB hb hε R hR))).homology k =
    ((operation α β r hr F B b hβ hB hb hε κ R hκ hκR hR).pre
      (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
        (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) ≫
        inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
          (BoundedCarrierJoinCap.rectangles α β r hr F B κ))).homology k := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro q
    dsimp only [DegreeLoweringHomology.Map.pre, DegreeLoweringHomology.Map.post, operation,
      BoundedCarrierExternalJoin.operation]
    rw [HomologicalComplex.comp_f]
    have hs := BoundedCarrierJoinCover.on_small α β r hr F B κ R hκ hκR q
    have ht := congrArg (fun z =>
      (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
        (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ)
        (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f ((m + 1) + q) ≫ z ≫
          (push (joinMap α β r hr F B b hβ hB hb hε R hR)).f q) hs
    simpa only [Category.assoc] using ht.symm

  rw [he, DegreeLoweringHomology.Map.pre_homology, operation_homology α β r hr F B b hβ hB hb hε κ R hκ hκR hR hm k,
    DegreeLoweringHomology.Map.pre_homology]

end
end Finsler.BoundedCarrierLengthProduct
