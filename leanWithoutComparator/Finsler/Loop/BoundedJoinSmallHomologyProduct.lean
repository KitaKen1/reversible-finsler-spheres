module

public import Finsler.Loop.SmallCrossHomologyBridge
public import Finsler.Loop.BoundedFixedScaleCoupledProduct
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains

/-! On actual small homology inputs, the genuine closed filtered join
is the specified separately strict-length product after the actual two
retained input maps, with the original kappa/R and real coefficients. -/

@[expose] public section
namespace Finsler.BoundedJoinSmallHomologyProduct

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
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

include hB hb in
theorem homology_factor (hm : 1 ≤ m) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    homologyCross (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
      (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) i j ((m + 1) + k) hij ≫
    ((BoundedCarrierExternalJoin.operation α β r hr F (a - L + 3 * ε) κ R hκ hκR).post
      (push (BoundedCarrierFilteredOutput.joinMap α β r hr F hε R hR hRu (L := L) hab hβ))).homology k =
    (homologyMap (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
      push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε))) i ⊗ₘ
    homologyMap (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) ≫
      push (StrictLengthProductFamilies.rightInput β F b hβ)) j) ≫
    FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij ≫
      (StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k := by
  rw [BoundedFixedScaleCoupledProduct.tensor_homology_factor α β r hr F hε R hR hRu (L := L)
    hab hβ hB hb κ hκ hκR hm k]
  rw [StrictLengthProductFamilies.pairInput, BoundedKeptProductInputs.short_input α r hr F (a - L + 3 * ε)]
  have hi : inclusion
      (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)) ⊗ TopCat.of Q)
      (SmallRectangleShuffle.rectangles (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)
        (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) =
      inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε) × Q))
        (BoundedCarrierJoinCap.rectangles α β r hr F (a - L + 3 * ε) κ) := rfl
  rw [← hi]
  have hs := SmallCrossHomologyBridge.small_cross
    (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε))) (Y := TopCat.of Q)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)
    (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j ((m + 1) + k) hij
  have hs' := congrArg (fun z => z ≫
    homologyMap (push (StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F (a - L + 3 * ε)) β F
      (a - L + 3 * ε) b (BoundedKeptProductInputs.length_lt α r hr F (a - L + 3 * ε)) hβ)) ((m + 1) + k) ≫
      (StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k) hs
  rw [show StrictLengthProductFamilies.pairInput (BoundedKeptProductInputs.kept α r hr F (a - L + 3 * ε)) β F
      (a - L + 3 * ε) b (BoundedKeptProductInputs.length_lt α r hr F (a - L + 3 * ε)) hβ =
      FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε) ⊗ₘ
        StrictLengthProductFamilies.rightInput β F b hβ by
    rw [StrictLengthProductFamilies.pairInput, BoundedKeptProductInputs.short_input]] at hs'
  have hn := CrossProjectionZero.cross_naturality
    (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε))
    (StrictLengthProductFamilies.rightInput β F b hβ) i j ((m + 1) + k) hij
  change (homologyMap (push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε))) i ⊗ₘ
      homologyMap (push (StrictLengthProductFamilies.rightInput β F b hβ)) j) ≫
      FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij =
    FilteredBilinearLoopProduct.crossMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (TopCat.of Q) i j ((m + 1) + k) hij ≫
      homologyMap (push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε) ⊗ₘ
        StrictLengthProductFamilies.rightInput β F b hβ)) ((m + 1) + k) at hn
  simp only [Category.assoc] at hs'
  rw [← Category.assoc (FilteredBilinearLoopProduct.crossMap
    (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (TopCat.of Q) i j ((m + 1) + k) hij), ← hn] at hs'
  simpa only [homologyMap_comp, Category.assoc, tensorHom_comp_tensorHom_assoc,
    BoundedCarrierJoinCap.rectangles, StrictLengthProductFamilies.pairInput,
    BoundedKeptProductInputs.short_input] using hs'

end
end Finsler.BoundedJoinSmallHomologyProduct
