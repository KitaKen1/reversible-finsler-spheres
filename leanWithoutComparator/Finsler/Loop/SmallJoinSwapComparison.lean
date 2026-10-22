module

public import Finsler.Loop.NearJoinSwapHomotopy
public import Finsler.Loop.SmallThomSwap
public import Finsler.Loop.CompactSmallJoinComparison

/-! Restrict the genuine bounded interchange homotopy to any sufficiently
small family neighborhood. Both genuine raw length products are compared
inside the identical specified strict output sublevel. -/

@[expose] public section
namespace Finsler.SmallJoinSwapComparison
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.StrictLengthEnergyBridge Finsler.FarNormalizedDiagonalCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
  (F : ReversibleMetric (m + 1)) (a b : ℝ)
  (hα : ∀ x, SobolevLength.length F (α x) < a) (hβ : ∀ y, SobolevLength.length F (β y) < b)
  (ha : 0 < a) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε)
  (s : ℝ) (hsJ : s ≤ NearJoinSwapHomotopy.radius F a b ha hb hε)

def pairMap : TopCat.of (P × Q) ⟶ TopCat.of (SphereLoop (m + 1) × SphereLoop (m + 1)) :=
  TopCat.ofHom ⟨fun z => (α z.1, β z.2),
    (α.continuous.comp continuous_fst).prodMk (β.continuous.comp continuous_snd)⟩

def toDomain : TopCat.of (CompactNormalizedJoinCapComparison.near α β s) ⟶
    TopCat.of (NearJoinSwapHomotopy.domain F a b ha hb hε) :=
  restriction (pairMap α β) (CompactNormalizedJoinCapComparison.near α β s)
    (NearJoinSwapHomotopy.domain F a b ha hb hε)
    (fun z hz => ⟨hz.trans_le hsJ, hα z.1, hβ z.2⟩)

variable (hsAB : s < StrictLengthProductJoinComparison.radius F a b ha hb hε)
  (hsBA : s < StrictLengthProductJoinComparison.radius F b a hb ha hε)
  (C : ℝ) (hbudget : a + (b + ε) ≤ C)

def firstRaw := CompactSmallJoinComparison.toProduct α β F a b hα hβ ha hb hε s hsAB ≫
  StrictLengthProductFamilies.rawJoin α β F a b hα hβ ha hb hε ≫
  OriginalLengthProductBudget.outputInclusion F hbudget

def swappedRaw := SmallThomSwap.nearSwap α β s ≫
  CompactSmallJoinComparison.toProduct β α F b a hβ hα hb ha hε s hsBA ≫
  StrictLengthProductFamilies.rawJoin β α F b a hβ hα hb ha hε ≫
  OriginalLengthProductBudget.outputInclusion F (by linarith : b + (a + ε) ≤ C)

theorem first_square : firstRaw α β F a b hα hβ ha hb hε s hsAB C hbudget =
    toDomain α β F a b hα hβ ha hb hε s hsJ ≫
      NearJoinSwapHomotopy.first F a b ha hb hε C hbudget := by
  ext z : 1
  apply Subtype.ext
  exact StrictLengthProductFamilies.rawJoin_formula α β F a b hα hβ ha hb hε _

theorem swapped_square : swappedRaw α β F a b hα hβ ha hb hε s hsBA C hbudget =
    toDomain α β F a b hα hβ ha hb hε s hsJ ≫
      NearJoinSwapHomotopy.swappedFirst F a b ha hb hε C hbudget := by
  ext z : 1
  apply Subtype.ext
  change (StrictLengthProductFamilies.rawJoin β α F b a hβ hα hb ha hε
    (CompactSmallJoinComparison.toProduct β α F b a hβ hα hb ha hε s hsBA
      (SmallThomSwap.nearSwap α β s z))).val =
    (NearJoinSwapHomotopy.swappedFirst F a b ha hb hε C hbudget
      (toDomain α β F a b hα hβ ha hb hε s hsJ z)).val
  rw [StrictLengthProductFamilies.rawJoin_formula, NearJoinSwapHomotopy.swappedFirst_formula]
  rfl

include hsJ in
theorem homology_eq (q : ℕ) :
    HomologicalComplex.homologyMap (push (firstRaw α β F a b hα hβ ha hb hε s hsAB C hbudget)) q =
    HomologicalComplex.homologyMap (push (swappedRaw α β F a b hα hβ ha hb hε s hsBA C hbudget)) q := by
  rw [first_square α β F a b hα hβ ha hb hε s hsJ hsAB C hbudget,
    swapped_square α β F a b hα hβ ha hb hε s hsJ hsBA C hbudget,
    push_comp, push_comp, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    NearJoinSwapHomotopy.homology_eq]

end
end Finsler.SmallJoinSwapComparison
