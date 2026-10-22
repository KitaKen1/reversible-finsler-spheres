module

public import Finsler.Topology.LevelCount

/-! The number of critical levels in a window. With finitely many prime closed geodesic images,
every critical level is a natural multiple of one of finitely many positive prime levels, so the
number of critical levels in an interval [a, a + L] is bounded independently of a. -/

@[expose] public section

namespace Finsler.WindowCount

open Set Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels

variable {n : ℕ} (F : ReversibleMetric n)

/-- With finitely many prime closed geodesic images, the number of critical levels in an
interval of length L is bounded independently of the interval. -/
theorem exists_window_count (hfin : (primeImages F).Finite) (L : ℝ) :
    ∃ K : ℕ, ∀ a : ℝ, (crit F ∩ Icc a (a + L)).ncard ≤ K := by
  classical
  have hP := primeLevels_finite F hfin
  refine ⟨∑ l ∈ hP.toFinset, (⌊L / l⌋₊ + 1), fun a => ?_⟩
  have hsub : crit F ∩ Icc a (a + L) ⊆
      ((hP.toFinset.biUnion fun l =>
        (Finset.Icc ⌈a / l⌉₊ (⌈a / l⌉₊ + ⌊L / l⌋₊)).image fun j : ℕ => (j : ℝ) * l :
          Finset ℝ) : Set ℝ) := by
    rintro c ⟨hc, hac, hca⟩
    obtain ⟨l, hl, j, rfl⟩ := crit_eq_multiple F hc
    have hlpos := primeLevels_pos F hl
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨l, hP.mem_toFinset.mpr hl,
      Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩⟩
    · exact Nat.ceil_le.mpr ((div_le_iff₀ hlpos).mpr hac)
    · have h1 : (j : ℝ) ≤ a / l + L / l := by
        rw [← add_div]
        exact (le_div_iff₀ hlpos).mpr hca
      have h2 : a / l ≤ (⌈a / l⌉₊ : ℝ) := Nat.le_ceil _
      by_cases hle : j ≤ ⌈a / l⌉₊
      · exact hle.trans (Nat.le_add_right _ _)
      · have hlt : ⌈a / l⌉₊ ≤ j := (not_le.mp hle).le
        have h4 : j - ⌈a / l⌉₊ ≤ ⌊L / l⌋₊ := by
          refine Nat.le_floor ?_
          rw [Nat.cast_sub hlt]
          linarith
        omega
  have h1 := ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [ncard_coe_finset] at h1
  refine h1.trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l _ => ?_))
  refine Finset.card_image_le.trans ?_
  rw [Nat.card_Icc]
  omega

end Finsler.WindowCount
