module

public import Finsler.Geometry.LevelCrossing

/-! A label is a direct summand of the crossing. On a compact band [a₀, b₀] around a level c₀,
let a descent decrease the function strictly in time one at every point of the band outside the
union of two disjoint open sets Z and R, and at every point of the band whose value is not c₀.
Then for all sufficiently tight cuts a < c₀ < c and times T ≥ 1, in every degree in which the
crossing pair at the wide cuts is finite dimensional, the lens pair of Z is finite dimensional
of dimension at most that of the crossing pair: the crossing at the tight cuts is the crossing at
the wide cuts (the strips contain no value c₀), and it is the sum of the lens pairs of Z and R. -/

@[expose] public section

namespace Finsler.RootLens

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation Finsler.LensFamily
open Finsler.LevelCrossing Module

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- **A label is at most the crossing.** -/
theorem lens_le_cross {W : TopCat.{0}} {h : W → ℝ} (D : Descent W h) (hc : Continuous h)
    {a₀ b₀ c₀ : ℝ} (ha₀ : a₀ < c₀) (hb₀ : c₀ < b₀)
    (hK : IsCompact {w : W | a₀ ≤ h w ∧ h w ≤ b₀}) {Z R : Set W} (hZ : IsOpen Z)
    (hR : IsOpen R) (hZR : Disjoint Z R)
    (hout : ∀ w, a₀ ≤ h w → h w ≤ b₀ → w ∉ Z ∪ R → h (D.flow 1 w) < h w)
    (hval : ∀ w, a₀ ≤ h w → h w ≤ b₀ → h w ≠ c₀ → h (D.flow 1 w) < h w)
    (hab₀ : a₀ ≤ b₀) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d → ∀ q : ℕ,
      Module.Finite (ZMod 2) (crossH h hab₀ q) →
      Module.Finite (ZMod 2) (lensH D Z a c t q) ∧
        finrank (ZMod 2) (lensH D Z a c t q) ≤ finrank (ZMod 2) (crossH h hab₀ q) := by
  classical
  set 𝒲 : Bool → Set W := fun i => cond i Z R with h𝒲
  have hopen : ∀ i ∈ (Finset.univ : Finset Bool), IsOpen (𝒲 i) := by
    intro i _
    cases i
    · exact hR
    · exact hZ
  have hdis : ((Finset.univ : Finset Bool) : Set Bool).PairwiseDisjoint 𝒲 := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact hZR.symm
    · exact hZR
    · exact absurd rfl hij
  have hstrict : ∀ w, a₀ ≤ h w → h w ≤ b₀ → w ∉ ⋃ i ∈ (Finset.univ : Finset Bool), 𝒲 i →
      h (D.flow 1 w) < h w := by
    intro w h1 h2 hw
    refine hout w h1 h2 fun hZR' => hw ?_
    rcases hZR' with hz | hr
    · exact Set.mem_iUnion₂.mpr ⟨true, Finset.mem_univ _, hz⟩
    · exact Set.mem_iUnion₂.mpr ⟨false, Finset.mem_univ _, hr⟩
  obtain ⟨dF, hdF, hfam⟩ := exists_family_decomposition D hc hK Finset.univ hopen hdis hstrict
  refine ⟨min (dF / 2) (min (c₀ - a₀) (b₀ - c₀)),
    lt_min (half_pos hdF) (lt_min (by linarith) (by linarith)),
    fun a c t ht ha hc' hca q hfin => ?_⟩
  have hca1 : c - a < dF / 2 := lt_of_lt_of_le hca (min_le_left _ _)
  have hca2 : c - a < c₀ - a₀ := lt_of_lt_of_le hca ((min_le_right _ _).trans (min_le_left _ _))
  have hca3 : c - a < b₀ - c₀ :=
    lt_of_lt_of_le hca ((min_le_right _ _).trans (min_le_right _ _))
  have haw : a₀ < a := by linarith
  have hcb : c < b₀ := by linarith
  have hac : a ≤ c := by linarith
  have hK₁ : IsCompact {w : W | a₀ ≤ h w ∧ h w ≤ a} :=
    hK.of_isClosed_subset ((isClosed_le continuous_const hc).inter
      (isClosed_le hc continuous_const)) fun w hw => ⟨hw.1, hw.2.trans (hac.trans hcb.le)⟩
  have hK₂ : IsCompact {w : W | c ≤ h w ∧ h w ≤ b₀} :=
    hK.of_isClosed_subset ((isClosed_le continuous_const hc).inter
      (isClosed_le hc continuous_const)) fun w hw => ⟨(haw.le.trans hac).trans hw.1, hw.2⟩
  have hmove := cross_move D hc haw.le hac hcb.le hK₁ hK₂
    (fun w h1 h2 => hval w h1 (h2.trans (hac.trans hcb.le)) (by intro he; linarith))
    (fun w h1 h2 => hval w ((haw.le.trans hac).trans h1) h2 (by intro he; linarith))
    rfl rfl hab₀ q
  have ha'a : max a₀ (c - dF / 2) < a := max_lt haw (by linarith)
  have hca' : c - max a₀ (c - dF / 2) < dF := by
    have := le_max_right a₀ (c - dF / 2)
    linarith
  obtain ⟨-, hsum, hlab⟩ := hfam (max a₀ (c - dF / 2)) a c t hac (le_max_left _ _) ha'a hcb.le
    hca' ht q
  have hfin' := hmove.1.mp hfin
  have hall := hlab hfin'
  have hZt : 𝒲 true = Z := rfl
  have hZfin := hall true (Finset.mem_univ _)
  rw [hZt] at hZfin
  refine ⟨hZfin, ?_⟩
  rw [hmove.2, (hsum hall).2, Fintype.sum_bool, hZt]
  exact Nat.le_add_right _ _

end

end Finsler.RootLens
