module

public import Finsler.Loop.SmallJoinSwapComparison
public import Finsler.Loop.BoundedCarrierEmpty

/-! The genuine strict-length product, on all separately bounded H1
families, is invariant under interchange of the two source spaces.
The comparison takes place in the same literal short target. -/

@[expose] public section
namespace Finsler.FamilyLengthProductSwap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
  (F : ReversibleMetric (m + 1)) (a b : ℝ)
  (hα : ∀ x, SobolevLength.length F (α x) < a) (hβ : ∀ y, SobolevLength.length F (β y) < b)
  {ε : ℝ} (hε : 0 < ε) (C : ℝ) (hbudget : a + (b + ε) ≤ C)

theorem small_factor (ha : 0 < a) (hb : 0 < b) (s : ℝ) (hs : 0 < s)
    (hsP : s < StrictLengthProductJoinComparison.radius F a b ha hb hε) (k : ℕ) :
    ((OriginalLengthProductBudget.operation F hbudget (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ))).homology k =
    (CompactSpecifiedCapShrink.smallOperation α β s hs).homology k ≫
      HomologicalComplex.homologyMap
        (push (SmallJoinSwapComparison.firstRaw α β F a b hα hβ ha hb hε s hsP C hbudget)) k := by
  rw [OriginalLengthProductBudget.operation, DegreeLoweringHomology.Map.pre_homology,
    DegreeLoweringHomology.Map.post_homology, ← Category.assoc,
    ← DegreeLoweringHomology.Map.pre_homology,
    StrictLengthProductFamilies.operation_factor α β F a b hα hβ ha hb hε (dim_pos m) k,
    StrictLengthProductFamilies.geometricOperation, DegreeLoweringHomology.Map.post_homology,
    CompactSmallJoinComparison.thom_shrink α β F a b hα hβ ha hb hε s hs hsP k]
  simp only [SmallJoinSwapComparison.firstRaw, push_comp, HomologicalComplex.homologyMap_comp,
    Category.assoc]

theorem positive_homology (ha : 0 < a) (hb : 0 < b) (hm : 1 ≤ m) (k : ℕ) :
    ((OriginalLengthProductBudget.operation F hbudget (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ))).homology k =
    HomologicalComplex.homologyMap (push (SmallThomSwap.swap (P := P) (Q := Q))) ((m + 1) + k) ≫
      ((OriginalLengthProductBudget.operation F (by linarith : b + (a + ε) ≤ C) (dim_pos m) hε).pre
        (push (StrictLengthProductFamilies.pairInput β α F b a hβ hα))).homology k := by
  let rAB := StrictLengthProductJoinComparison.radius F a b ha hb hε
  let rBA := StrictLengthProductJoinComparison.radius F b a hb ha hε
  let rJ := NearJoinSwapHomotopy.radius F a b ha hb hε
  let s := min rAB (min rBA rJ) / 2
  have hAB : 0 < rAB := StrictLengthProductJoinComparison.radius_pos F a b ha hb hε
  have hBA : 0 < rBA := StrictLengthProductJoinComparison.radius_pos F b a hb ha hε
  have hJ : 0 < rJ := NearJoinSwapHomotopy.radius_pos F a b ha hb hε
  have hs : 0 < s := div_pos (lt_min hAB (lt_min hBA hJ)) (by norm_num)
  have hsmall : s < min rAB (min rBA rJ) := by dsimp [s]; linarith [lt_min hAB (lt_min hBA hJ)]
  have hsAB : s < rAB := hsmall.trans_le (min_le_left _ _)
  have hsBA : s < rBA := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hsJ : s ≤ rJ := ((hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).le
  rw [small_factor α β F a b hα hβ hε C hbudget ha hb s hs hsAB k,
    SmallJoinSwapComparison.homology_eq α β F a b hα hβ ha hb hε s hsJ hsAB hsBA C hbudget k,
    small_factor β α F b a hβ hα hε C (by linarith) hb ha s hs hsBA k]
  have he := SmallThomSwap.homology_eq α β s hs hm k
  simpa only [SmallJoinSwapComparison.swappedRaw, SmallJoinSwapComparison.firstRaw,
    push_comp, HomologicalComplex.homologyMap_comp, Category.assoc] using
    (congrArg (fun f => f ≫ HomologicalComplex.homologyMap
      (push (SmallJoinSwapComparison.firstRaw β α F b a hβ hα hb ha hε s hsBA C (by linarith))) k) he).symm

theorem homology (hm : 1 ≤ m) (k : ℕ) :
    ((OriginalLengthProductBudget.operation F hbudget (dim_pos m) hε).pre
      (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ))).homology k =
    HomologicalComplex.homologyMap (push (SmallThomSwap.swap (P := P) (Q := Q))) ((m + 1) + k) ≫
      ((OriginalLengthProductBudget.operation F (by linarith : b + (a + ε) ≤ C) (dim_pos m) hε).pre
        (push (StrictLengthProductFamilies.pairInput β α F b a hβ hα))).homology k := by
  by_cases hpos : 0 < a ∧ 0 < b
  · exact positive_homology α β F a b hα hβ hε C hbudget hpos.1 hpos.2 hm k
  · have hpos' : ¬ (0 < b ∧ 0 < a) := fun h => hpos ⟨h.2, h.1⟩
    rw [DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology,
      OriginalLengthProductBudget.nonpos_homology F hbudget (dim_pos m) hε hpos,
      OriginalLengthProductBudget.nonpos_homology F (by linarith : b + (a + ε) ≤ C) (dim_pos m) hε hpos',
      comp_zero, comp_zero, comp_zero]

end
end Finsler.FamilyLengthProductSwap
