module

public import Finsler.Topology.CrossingSlopes
public import Finsler.Topology.ComparisonRank
public import Finsler.Topology.CrossingW

/-! The rank inputs from the global input on the loop space. With finitely many prime closed
geodesic images, the fields of the rank inputs which concern single crossings follow from the
uniform bounds: the ordinary and reflection Borel groups of single crossings have dimension at
most B; in a degree j above A a single crossing has nonzero reflection Borel group only if one of
its critical levels l is active for j, that is |j - s l| ≤ A for a positive slope s (forgetting
the action is injective on single crossings because w acts as zero there, and the ordinary groups
are supported near the slope lines); and the active critical levels of a degree lie in finitely
many windows of bounded length, so their number is bounded. Hence the rank inputs exist as soon
as the images of the ordinary restriction from the loop space are bounded in the degrees up to
any given degree. -/

@[expose] public section

namespace Finsler.RankAssembly

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.CriticalLevels Finsler.ComparisonRank Finsler.CrossingSlopes
open Finsler.CriticalCircles

noncomputable section

/-- The number of elements of a finite union is at most the sum of the numbers. -/
theorem ncard_biUnion_le {α ι : Type*} (T : Finset ι) (X : ι → Set α) :
    (⋃ i ∈ T, X i).ncard ≤ ∑ i ∈ T, (X i).ncard := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hx]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

variable {n : ℕ} (F : ReversibleMetric n)

set_option maxHeartbeats 1600000 in
/-- **The rank inputs from the global input on the loop space.** -/
theorem nonempty_rankInputs (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a₀ : ℝ}
    (hres : ∀ J : ℕ, ∃ G : ℕ, ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, i ≤ J →
      finrank (ZMod 2) (LinearMap.range (Hmap (resHom F a) i)) ≤ G) :
    Nonempty (RankInputs F a₀) := by
  classical
  obtain ⟨B, -, -, -, hrank, -⟩ := exists_crossing_slopes F hn hfin
  obtain ⟨A, hsupp⟩ := exists_single_support F hn hfin
  set Sp : Finset ℝ := (insert (0 : ℝ) ((labels F hfin).image (slope F))).filter
    (fun s => 0 < s) with hSp
  have hwin : ∀ s ∈ Sp, ∃ K : ℕ, ∀ x : ℝ, (crit F ∩ Icc x (x + 2 * A / s)).ncard ≤ K :=
    fun s _ => Finsler.WindowCount.exists_window_count F hfin _
  choose! Kw hKw using hwin
  obtain ⟨G, hG⟩ := hres A
  refine ⟨{
    C := B
    K := ∑ s ∈ Sp, Kw s
    jlow := A
    act := fun j => {l : ℝ | ∃ s ∈ Sp, |(j : ℝ) - s * l| ≤ A}
    cross_rank := ?_
    act_count := ?_
    Cord := B
    cross_ord := fun a' b' hab' ha' hac hbc hsub i _ =>
      (hrank a' b' hab' ha' hac hbc hsub (i + 1)).1
    G := G
    res_rank := fun a ha i hi => hG a ha i hi }⟩
  · intro j hj a' b' hab' ha' hac hbc hsub
    refine ⟨(hrank a' b' hab' ha' hac hbc hsub j).2, fun hact z => ?_⟩
    by_contra hz
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hinj := Finsler.CrossingW.cross_forget_injective F hn hfin hab' ha' hac hbc hsub j'
    have hz' : forget (crossComplex F hab') (j' + 1) z ≠ 0 := fun h =>
      hz (hinj (h.trans (map_zero _).symm))
    obtain ⟨c₀, ⟨hc₀, h1, h2⟩, s, hs, hle⟩ :=
      hsupp a' b' hab' ha' hac hbc hsub (j' + 1) ⟨_, hz'⟩
    have hc₀pos : 0 < c₀ := ha'.trans_le h1
    have hspos : 0 < s := by
      by_contra hs0
      have hsc : s * c₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hs0) hc₀pos.le
      have hjA : (A : ℝ) < ((j' + 1 : ℕ) : ℝ) := by exact_mod_cast hj
      rw [abs_le] at hle
      linarith [hle.2]
    exact hact c₀ ⟨hc₀, h1, h2⟩ ⟨s, Finset.mem_filter.mpr ⟨hs, hspos⟩, hle⟩
  · intro j _ a
    have hsub : crit F ∩ Icc 0 a ∩ {l : ℝ | ∃ s ∈ Sp, |(j : ℝ) - s * l| ≤ A} ⊆
        ⋃ s ∈ Sp, crit F ∩ Icc (((j : ℝ) - A) / s) (((j : ℝ) - A) / s + 2 * A / s) := by
      rintro l ⟨⟨hl, -⟩, s, hs, hle⟩
      have hspos : 0 < s := (Finset.mem_filter.mp hs).2
      refine mem_iUnion₂.mpr ⟨s, hs, hl, ?_, ?_⟩
      · rw [div_le_iff₀ hspos]
        rw [abs_le] at hle
        linarith [hle.2]
      · rw [← add_div, le_div_iff₀ hspos]
        rw [abs_le] at hle
        linarith [hle.1]
    have hfinU : (⋃ s ∈ Sp, crit F ∩ Icc (((j : ℝ) - A) / s)
        (((j : ℝ) - A) / s + 2 * A / s)).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet Sp) fun s _ => crit_finite F hfin _ _
    calc (crit F ∩ Icc 0 a ∩ {l : ℝ | ∃ s ∈ Sp, |(j : ℝ) - s * l| ≤ A}).ncard
        ≤ (⋃ s ∈ Sp, crit F ∩ Icc (((j : ℝ) - A) / s)
            (((j : ℝ) - A) / s + 2 * A / s)).ncard := Set.ncard_le_ncard hsub hfinU
      _ ≤ ∑ s ∈ Sp, (crit F ∩ Icc (((j : ℝ) - A) / s)
            (((j : ℝ) - A) / s + 2 * A / s)).ncard := ncard_biUnion_le Sp _
      _ ≤ ∑ s ∈ Sp, Kw s := Finset.sum_le_sum fun s hs => hKw s hs _

end

end Finsler.RankAssembly
