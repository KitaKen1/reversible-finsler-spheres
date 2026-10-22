module

public import Finsler.Analysis.LevelAssembly
public import Finsler.Analysis.LevelGlue

/-! The field and the deformed function of a level. Let f be a function on a finite dimensional
real normed space, differentiable on an open set O, and B a set (the band). For finitely many
labels i let U_i ⊆ O be pairwise disjoint open sets, W_i fields smooth on U_i along which f does
not increase on U_i and decreases strictly on U_i outside a set C_i (the critical circle), β_i
deformations with compact closed supports along which f + β_i does not increase on the closed
support of β_i and decreases strictly there outside C_i, and T_i ⊆ U_i compact sets containing
the closed support of β_i. Suppose that for every open set 𝒲 containing the critical points of
the band there is a band field: smooth, compactly supported in O, along which f does not
increase on O and decreases strictly at the points of B outside 𝒲, and that the critical points
of the band lie in the union of the T_i. Then there is a smooth compactly supported field V,
supported in O, equal to W_i on T_i, along which f + Σ β_i does not increase on O and decreases
strictly at every point of B outside the union of the C_i. The field glues the W_i to the band
field for 𝒲 = the union of the open sets on which the cutoffs are 1. -/

@[expose] public section

namespace Finsler.LevelBuild

open Set Filter
open Finsler.GlueField Finsler.LevelGlue Finsler.LevelAssembly
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*}

/-- **The field and the deformed function of a level.** -/
theorem exists_level_field (s : Finset ι) {f : E → ℝ} {O B Crit : Set E}
    {U : ι → Set E} {W : ι → E → E} {β : ι → E → ℝ} {C T : ι → Set E}
    (hU : ∀ i ∈ s, IsOpen (U i)) (hUO : ∀ i ∈ s, U i ⊆ O)
    (hUdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (hW : ∀ i ∈ s, ContDiffOn ℝ ∞ (W i) (U i))
    (hWle : ∀ i ∈ s, ∀ y ∈ U i, fderiv ℝ f y (W i y) ≤ 0)
    (hWlt : ∀ i ∈ s, ∀ y ∈ U i, y ∉ C i → fderiv ℝ f y (W i y) < 0)
    (hT : ∀ i ∈ s, IsCompact (T i)) (hTU : ∀ i ∈ s, T i ⊆ U i)
    (hβT : ∀ i ∈ s, tsupport (β i) ⊆ T i)
    (hβle : ∀ i ∈ s, ∀ y ∈ tsupport (β i), fderiv ℝ (fun y => f y + β i y) y (W i y) ≤ 0)
    (hβlt : ∀ i ∈ s, ∀ y ∈ tsupport (β i), y ∉ C i →
      fderiv ℝ (fun y => f y + β i y) y (W i y) < 0)
    (hcrit : Crit ⊆ ⋃ i ∈ s, T i)
    (hband : ∀ 𝒲 : Set E, IsOpen 𝒲 → Crit ⊆ 𝒲 → ∃ V : E → E, ContDiff ℝ ∞ V ∧
      HasCompactSupport V ∧ tsupport V ⊆ O ∧ (∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) ∧
      ∀ y ∈ B, y ∉ 𝒲 → fderiv ℝ f y (V y) < 0) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ O ∧
      (∀ i ∈ s, ∀ y ∈ T i, V y = W i y) ∧
      (∀ y ∈ O, fderiv ℝ (fun y => f y + ∑ j ∈ s, β j y) y (V y) ≤ 0) ∧
      ∀ y ∈ O, y ∈ B → (∀ i ∈ s, y ∉ C i) →
        fderiv ℝ (fun y => f y + ∑ j ∈ s, β j y) y (V y) < 0 := by
  classical
  -- cutoffs equal to 1 near T_i and supported in U_i
  have hcut : ∀ i, ∃ (χ : E → ℝ) (Wi : Set E), i ∈ s → (ContDiff ℝ ∞ χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U i ∧ IsOpen Wi ∧
      T i ⊆ Wi ∧ ∀ y ∈ Wi, χ y = 1) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨χ, Wi, h⟩ := exists_cutoff (hT i hi) (hU i hi) (hTU i hi)
      exact ⟨χ, Wi, fun _ => h⟩
    · exact ⟨0, ∅, fun h => absurd h hi⟩
  choose χ Wc hχ using hcut
  have hχs : ∀ i ∈ s, ContDiff ℝ ∞ (χ i) := fun i hi => (hχ i hi).1
  have hχ01 : ∀ i ∈ s, ∀ y, 0 ≤ χ i y ∧ χ i y ≤ 1 := fun i hi => (hχ i hi).2.1
  have hχc : ∀ i ∈ s, HasCompactSupport (χ i) := fun i hi => (hχ i hi).2.2.1
  have hχU : ∀ i ∈ s, tsupport (χ i) ⊆ U i := fun i hi => (hχ i hi).2.2.2.1
  have hWco : ∀ i ∈ s, IsOpen (Wc i) := fun i hi => (hχ i hi).2.2.2.2.1
  have hTW : ∀ i ∈ s, T i ⊆ Wc i := fun i hi => (hχ i hi).2.2.2.2.2.1
  have hχ1 : ∀ i ∈ s, ∀ y ∈ Wc i, χ i y = 1 := fun i hi => (hχ i hi).2.2.2.2.2.2
  have hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)) :=
    fun i hi j hj hij => (hUdis i hi j hj hij).mono (hχU i hi) (hχU j hj)
  have hWcsupp : ∀ i ∈ s, Wc i ⊆ tsupport (χ i) := fun i hi y hy =>
    subset_tsupport _ (by rw [Function.mem_support, hχ1 i hi y hy]; exact one_ne_zero)
  -- the band field strict outside the union of the Wc i
  set 𝒲 : Set E := ⋃ i ∈ s, Wc i with h𝒲def
  have h𝒲 : IsOpen 𝒲 := isOpen_biUnion fun i hi => hWco i hi
  have hcrit' : Crit ⊆ 𝒲 := hcrit.trans (biUnion_mono subset_rfl fun i hi => hTW i hi)
  obtain ⟨V, hV, hVc, hVt, hVle, hVlt⟩ := hband 𝒲 h𝒲 hcrit'
  -- the glued field
  have hβ1 : ∀ i ∈ s, ∀ y ∈ tsupport (β i), χ i y = 1 := fun i hi y hy =>
    hχ1 i hi y (hTW i hi (hβT i hi hy))
  refine ⟨sumGlue s U χ W V, sumGlue_contDiff hU hχs hχU hW hV,
    sumGlue_hasCompactSupport hχc hVc, ?_, ?_, ?_, ?_⟩
  · -- support
    have hsupp : Function.support (sumGlue s U χ W V) ⊆
        (⋃ i ∈ s, tsupport (χ i)) ∪ tsupport V := by
      intro y hy
      by_cases hin : ∃ i ∈ s, y ∈ tsupport (χ i)
      · obtain ⟨i, hi, hyi⟩ := hin
        exact Or.inl (mem_biUnion hi hyi)
      · right
        have hno : ∀ i ∈ s, y ∉ tsupport (χ i) := fun i hi h => hin ⟨i, hi, h⟩
        rw [Function.mem_support, sumGlue_eq_of_not_mem hno] at hy
        exact subset_tsupport V hy
    have hcl : IsClosed ((⋃ i ∈ s, tsupport (χ i)) ∪ tsupport V) :=
      (isClosed_biUnion_finset fun i _ => isClosed_tsupport (χ i)).union (isClosed_tsupport V)
    refine (closure_minimal hsupp hcl).trans (union_subset ?_ hVt)
    exact iUnion₂_subset fun i hi => (hχU i hi).trans (hUO i hi)
  · intro i hi y hy
    have hyW := hTW i hi hy
    rw [sumGlue_eq_glue hdis hi (hWcsupp i hi hyW), glue_of_eq_one (hχU i hi) (hχ1 i hi y hyW)]
  · intro y hy
    exact deform_descent hdis (fun i hi y => (hχ01 i hi y).1) (fun i hi y => (hχ01 i hi y).2) hχU
      hβ1 hβle (fun i hi y hyt => hWle i hi y (hχU i hi hyt)) hVle hy
  · intro y hy hyB hyC
    by_cases hin : ∃ i ∈ s, y ∈ tsupport (β i)
    · obtain ⟨i, hi, hyi⟩ := hin
      rw [fderiv_at_label hdis hβ1 hχU hi hyi]
      exact hβlt i hi y hyi (hyC i hi)
    · have hno : ∀ j ∈ s, y ∉ tsupport (β j) := fun j hj h => hin ⟨j, hj, h⟩
      rw [fderiv_off_labels hno]
      apply (sumGlue_descent f hdis (fun i hi y => (hχ01 i hi y).1)
        (fun i hi y => (hχ01 i hi y).2) hχU (fun i hi y hyt => hWle i hi y (hχU i hi hyt))
        hVle hy).2
      by_cases hχin : ∃ i ∈ s, y ∈ tsupport (χ i)
      · obtain ⟨i, hi, hyi⟩ := hχin
        right
        refine ⟨i, hi, hyi, ?_⟩
        by_cases h1 : χ i y < 1
        · left
          refine ⟨hVlt y hyB ?_, h1⟩
          intro hy𝒲
          obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy𝒲
          by_cases hji : j = i
          · subst hji
            exact (lt_irrefl _) (hχ1 j hj y hyj ▸ h1)
          · exact Set.disjoint_left.mp (hdis j hj i hi hji) (hWcsupp j hj hyj) hyi
        · right
          have hχ1' : χ i y = 1 := le_antisymm (hχ01 i hi y).2 (not_lt.mp h1)
          exact ⟨hWlt i hi y (hχU i hi hyi) (hyC i hi), by rw [hχ1']; exact one_pos,
            hχU i hi hyi⟩
      · left
        have hno' : ∀ i ∈ s, y ∉ tsupport (χ i) := fun i hi h => hχin ⟨i, hi, h⟩
        refine ⟨hno', hVlt y hyB ?_⟩
        intro hy𝒲
        obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy𝒲
        exact hno' j hj (hWcsupp j hj hyj)

end

end Finsler.LevelBuild
