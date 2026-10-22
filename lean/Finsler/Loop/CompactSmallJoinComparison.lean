module

public import Finsler.Loop.CompactSpecifiedCapShrink
public import Finsler.Loop.JoinedNativeCanonicalTime
public import Finsler.Loop.OriginalLengthProductBudget

/-! On a proof-only smaller near neighborhood, the actual original
joined family agrees with the genuine product raw join included in the
original specified short target. No native radius is changed. -/

@[expose] public section
namespace Finsler.CompactSmallJoinComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
  (F : ReversibleMetric (m + 1)) (a b : ℝ) (hα : ∀ x, SobolevLength.length F (α x) < a)
  (hβ : ∀ y, SobolevLength.length F (β y) < b) (ha : 0 < a) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε)
  (s : ℝ) (hs : 0 < s) (hsP : s < StrictLengthProductJoinComparison.radius F a b ha hb hε)

def toProduct : TopCat.of (CompactNormalizedJoinCapComparison.near α β s) ⟶
    TopCat.of (StrictLengthProductFamilies.tube α β F a b hα hβ ha hb hε) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, z.property.trans hsP⟩, continuous_subtype_val.subtype_mk _⟩

include hs in
theorem thom_shrink (q : ℕ) : (StrictLengthProductFamilies.thomOperation α β F a b hα hβ ha hb hε (dim_pos m)).homology q =
    (CompactSpecifiedCapShrink.smallOperation α β s hs).homology q ≫
      HomologicalComplex.homologyMap (push (toProduct α β F a b hα hβ ha hb hε s hsP)) q := by
  have he := DiagonalCutNaturality.homology_naturality (dim_pos m) (𝟙 (TopCat.of (P × Q)))
    (StrictLengthProductFamilies.leftEvaluation α (Q := Q)) (StrictLengthProductFamilies.rightEvaluation β (P := P))
    (CompactNormalizedJoinCapComparison.near α β s) (StrictLengthProductFamilies.tube α β F a b hα hβ ha hb hε)
    (CompactNormalizedJoinCapComparison.near_open α β s) (StrictLengthProductFamilies.tube_open α β F a b hα hβ ha hb hε)
    (CompactSpecifiedCapShrink.diagonal_in_near α β s hs) (StrictLengthProductFamilies.diagonal_in_tube α β F a b hα hβ ha hb hε)
    (fun _ hz => hz.trans hsP) q
  have hi : restriction (𝟙 (TopCat.of (P × Q))) (CompactNormalizedJoinCapComparison.near α β s)
      (StrictLengthProductFamilies.tube α β F a b hα hβ ha hb hε) (fun _ hz => hz.trans hsP) =
    toProduct α β F a b hα hβ ha hb hε s hsP := by ext z : 1; rfl
  rw [hi] at he
  simpa only [FarDiagonalCutComparison.push_identity, HomologicalComplex.homologyMap_id, Category.id_comp,
    StrictLengthProductFamilies.thomOperation, CompactSpecifiedCapShrink.smallOperation] using he

variable (R : ℝ) (hR : R ≤ 1 / 2) (hsR : s ≤ R) (C : ℝ) (hbudget : a + (b + ε) ≤ C)
  (hΓ : ∀ z, SobolevLength.length F (JoinedNativeCanonicalTime.joinedFamily α β R hR z) < C)

theorem raw_square : CompactSpecifiedCapShrink.intoCarrier α β R s hsR ≫
    CompactInputShortMaps.family (JoinedNativeCanonicalTime.joinedFamily α β R hR) F C hΓ =
    toProduct α β F a b hα hβ ha hb hε s hsP ≫
      StrictLengthProductFamilies.rawJoin α β F a b hα hβ ha hb hε ≫
      OriginalLengthProductBudget.outputInclusion F hbudget := by
  ext z : 1
  apply Subtype.ext
  change JoinedNativeCanonicalTime.joinedFamily α β R hR
      (CompactSpecifiedCapShrink.intoCarrier α β R s hsR z) =
    (StrictLengthProductFamilies.rawJoin α β F a b hα hβ ha hb hε
      (toProduct α β F a b hα hβ ha hb hε s hsP z)).val
  rw [StrictLengthProductFamilies.rawJoin_formula]
  rfl

end
end Finsler.CompactSmallJoinComparison
