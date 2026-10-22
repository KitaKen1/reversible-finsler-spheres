module

public import Finsler.Loop.BoundedSpecifiedCapShrink
public import Finsler.Loop.BoundedCarrierUniformRawJoin

/-! Only the specified Thom cap is shrunk. On the smaller actual open
near space, its raw join into the original fixed-scale length output
is literally the product model's raw join. The original closed carrier
radius is not required to be below the product radius. -/

@[expose] public section
namespace Finsler.BoundedSmallJoinComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) {ε : ℝ} (hε : 0 < ε)
  (R : ℝ) (hR : R ≤ 1 / 2) (hRu : R < BoundedCarrierUniformRawJoin.radius α β r hr F hε)
  (B b : ℝ) (hβ : ∀ y, SobolevLength.length F (β y) < b) (hB : 0 < B) (hb : 0 < b)
  (s : ℝ) (hs : 0 < s) (hsR : s ≤ R)
  (hsP : s < StrictLengthProductJoinComparison.radius F B b hB hb hε)

def toProduct : TopCat.of (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s) ⟶
    TopCat.of (StrictLengthProductFamilies.tube (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, z.property.trans hsP⟩, continuous_subtype_val.subtype_mk _⟩

theorem toProduct_source : toProduct α β r hr F hε B b hβ hB hb s hsP ≫
    SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (StrictLengthProductFamilies.tube (BoundedKeptProductInputs.kept α r hr F B) β F B b
        (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε) =
    SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s) := rfl

include hs in
theorem thom_shrink (q : ℕ) :
    (StrictLengthProductFamilies.thomOperation (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε (dim_pos m)).homology q =
    (BoundedSpecifiedCapShrink.smallOperation α β r hr F B s hs).homology q ≫
      HomologicalComplex.homologyMap (push (toProduct α β r hr F hε B b hβ hB hb s hsP)) q := by
  have he := DiagonalCutNaturality.homology_naturality (dim_pos m)
    (𝟙 (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)))
    (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B) (Q := Q))
    (StrictLengthProductFamilies.rightEvaluation β (P := FirstInputSelfCutBoundedSpace.bounded α r hr F B))
    (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s)
    (StrictLengthProductFamilies.tube (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε)
    (CompactNormalizedJoinCapComparison.near_open _ _ s)
    (StrictLengthProductFamilies.tube_open _ _ F B b _ hβ hB hb hε)
    (BoundedSpecifiedCapShrink.diagonal_in_near α β r hr F B s hs)
    (StrictLengthProductFamilies.diagonal_in_tube _ _ F B b _ hβ hB hb hε)
    (fun _ hz => hz.trans hsP) q
  have hi : restriction (𝟙 (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)))
      (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s)
      (StrictLengthProductFamilies.tube (BoundedKeptProductInputs.kept α r hr F B) β F B b
        (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε) (fun _ hz => hz.trans hsP) =
      toProduct α β r hr F hε B b hβ hB hb s hsP := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  rw [hi] at he
  simpa only [FarDiagonalCutComparison.push_identity, HomologicalComplex.homologyMap_id,
    Category.id_comp, StrictLengthProductFamilies.thomOperation, BoundedSpecifiedCapShrink.smallOperation] using he

theorem raw_square :
    BoundedSpecifiedCapShrink.intoCarrier α β r hr F B R s hsR ≫
      BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu B b hβ =
    toProduct α β r hr F hε B b hβ hB hb s hsP ≫
      StrictLengthProductFamilies.rawJoin (BoundedKeptProductInputs.kept α r hr F B) β F B b
        (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
    (BoundedKeptProductInputs.properTube α β r hr F B R
      (BoundedSpecifiedCapShrink.intoCarrier α β r hr F B R s hsR z)) =
    (StrictLengthProductFamilies.rawJoin (BoundedKeptProductInputs.kept α r hr F B) β F B b
      (BoundedKeptProductInputs.length_lt α r hr F B) hβ hB hb hε
      (toProduct α β r hr F hε B b hβ hB hb s hsP z)).val
  rw [StrictLengthProductFamilies.rawJoin_formula]
  rfl

end
end Finsler.BoundedSmallJoinComparison
