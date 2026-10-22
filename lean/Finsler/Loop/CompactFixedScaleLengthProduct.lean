module

public import Finsler.Loop.CompactSmallJoinComparison
public import Finsler.Loop.BoundedCarrierEmpty

/-! The actual original fixed-scale normalized spatial join followed
by the actual joined-family strict input IS the genuine length product
in that input target. No R<product-radius or positive individual bound
is required in the final result. The native geometry stays fixed. -/

@[expose] public section
namespace Finsler.CompactFixedScaleLengthProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (F : ReversibleMetric (m + 1))
  (a b : ℝ) (hα : ∀ x, SobolevLength.length F (α x) < a) (hβ : ∀ y, SobolevLength.length F (β y) < b)
  {ε : ℝ} (hε : 0 < ε) (R : ℝ) (hR : R ≤ 1 / 2) (C : ℝ) (hbudget : a + (b + ε) ≤ C)
  (hΓ : ∀ z, SobolevLength.length F (JoinedNativeCanonicalTime.joinedFamily α β R hR z) < C)
  {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R)


theorem positive_operation_homology (ha : 0 < a) (hb : 0 < b) (hm : 1 ≤ m) (k : ℕ) :
    ((CompactJoinCapLocalization.unrefined α β (dim_pos m) hκ hκR).post
      (push (CompactInputShortMaps.family (JoinedNativeCanonicalTime.joinedFamily α β R hR) F C hΓ))).homology k =
    ((OriginalLengthProductBudget.operation F hbudget (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ))).homology k := by
  have hRpos : 0 < R := lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 2) hκ) hκR
  have hκ2 : κ ≤ 2 := by linarith
  let s := min R (StrictLengthProductJoinComparison.radius F a b ha hb hε) / 2
  have hp := StrictLengthProductJoinComparison.radius_pos F a b ha hb hε
  have hs : 0 < s := div_pos (lt_min hRpos hp) (by norm_num)
  have hsR : s ≤ R := by dsimp [s]; linarith [min_le_left R (StrictLengthProductJoinComparison.radius F a b ha hb hε)]
  have hsP : s < StrictLengthProductJoinComparison.radius F a b ha hb hε := by
    dsimp [s]; linarith [min_le_right R (StrictLengthProductJoinComparison.radius F a b ha hb hε)]
  have hc := CompactSpecifiedCapShrink.homology_eq α β κ R hκ hκR s hs hsR hm hκ2 k
  have ht := CompactSmallJoinComparison.thom_shrink α β F a b hα hβ ha hb hε s hs hsP k
  have hj := CompactSmallJoinComparison.raw_square α β F a b hα hβ ha hb hε s hsP R hR hsR C hbudget hΓ
  rw [DegreeLoweringHomology.Map.post_homology, hc, DegreeLoweringHomology.Map.post_homology,
    Category.assoc, ← HomologicalComplex.homologyMap_comp, ← push_comp, hj, push_comp, push_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, ← Category.assoc, ← ht]
  simpa only [OriginalLengthProductBudget.operation, DegreeLoweringHomology.Map.pre_homology,
    DegreeLoweringHomology.Map.post_homology, StrictLengthProductFamilies.geometricOperation,
    ← Category.assoc] using congrArg
    (fun f => f ≫ HomologicalComplex.homologyMap (push (OriginalLengthProductBudget.outputInclusion F hbudget)) k)
    (StrictLengthProductFamilies.operation_factor α β F a b hα hβ ha hb hε (dim_pos m) k).symm


theorem operation_homology (hm : 1 ≤ m) (k : ℕ) :
    ((CompactJoinCapLocalization.unrefined α β (dim_pos m) hκ hκR).post
      (push (CompactInputShortMaps.family (JoinedNativeCanonicalTime.joinedFamily α β R hR) F C hΓ))).homology k =
    ((OriginalLengthProductBudget.operation F hbudget (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ))).homology k := by
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · exact positive_operation_homology α β F a b hα hβ hε R hR C hbudget hΓ hκ hκR ha hb hm k
    · have : IsEmpty Q := BoundedCarrierEmpty.family_empty β F hβ (le_of_not_gt hb)
      apply DegreeLoweringHomology.Map.homology_eq_of_components
      intro q
      exact (EmptySingularChains.chains_zero (TopCat.of (P × Q)) ((m + 1) + q)).eq_of_src _ _
  · have : IsEmpty P := BoundedCarrierEmpty.family_empty α F hα (le_of_not_gt ha)
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro q
    exact (EmptySingularChains.chains_zero (TopCat.of (P × Q)) ((m + 1) + q)).eq_of_src _ _

end
end Finsler.CompactFixedScaleLengthProduct
