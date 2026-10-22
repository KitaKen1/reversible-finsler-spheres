module

public import Finsler.Analysis.PseudoGradient
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Basic

/-! A pseudo-gradient which decreases the function at every non-critical point of a compact
set. Let f be C¹ on an open set O of a finite dimensional real normed space, K ⊆ O compact and Γ
closed, and suppose that the derivative of f does not vanish on K outside Γ. The compact sets
A_k = {x ∈ K | dist(x, Γ) ≥ 1/(k+1)} exhaust K \ Γ; pseudo-gradients V_k strict on A_k and
supported in a fixed thickening of K inside O are summed with weights ε_k so small that the
series of all iterated derivatives converges uniformly (mathlib `contDiff_tsum`). The sum V is
smooth, compactly supported in O, bounded by any prescribed κ > 0, the derivative of f in its
direction is the sum of the nonpositive derivatives in the directions of ε_k V_k, and it is
negative at every point of K \ Γ, where one term is negative. A field which is strict only away
from a neighbourhood of Γ does not suffice for comparing crossings at different cuts: its
non-strict points carry values near the critical value which cannot be compared with the
decrease outside the label sets in degenerate cases. -/

@[expose] public section

namespace Finsler.StrictField

open Set Filter Metric Finsler.PseudoGradient
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The points of K at distance at least 1/(k+1) from every point of Γ. -/
def layer (K Γ : Set E) (k : ℕ) : Set E := K ∩ {x | ∀ y ∈ Γ, 1 / ((k : ℝ) + 1) ≤ dist x y}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem layer_isClosed {K : Set E} (hK : IsClosed K) (Γ : Set E) (k : ℕ) :
    IsClosed (layer K Γ k) := by
  refine hK.inter ?_
  have h : {x : E | ∀ y ∈ Γ, 1 / ((k : ℝ) + 1) ≤ dist x y} =
      ⋂ y ∈ Γ, {x : E | 1 / ((k : ℝ) + 1) ≤ dist x y} := by
    ext x
    simp
  rw [h]
  exact isClosed_biInter fun y _ => isClosed_le continuous_const (continuous_id.dist continuous_const)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem not_mem_of_mem_layer {K Γ : Set E} {k : ℕ} {x : E} (hx : x ∈ layer K Γ k) : x ∉ Γ := by
  intro hxΓ
  have h := hx.2 x hxΓ
  rw [dist_self] at h
  have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem exists_layer {K Γ : Set E} (hΓ : IsClosed Γ) {x : E} (hxK : x ∈ K) (hxΓ : x ∉ Γ) :
    ∃ k : ℕ, x ∈ layer K Γ k := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΓ.isOpen_compl x hxΓ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨k, hxK, fun y hy => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hy' : y ∈ ball x ε := by
    rw [mem_ball, dist_comm]
    linarith
  exact hball hy' hy

/-- **A pseudo-gradient strict at every non-critical point of a compact set.** -/
theorem exists_strict_field {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O)
    {K Γ : Set E} (hK : IsCompact K) (hKO : K ⊆ O) (hΓ : IsClosed Γ)
    (hne : ∀ x ∈ K, x ∉ Γ → fderiv ℝ f x ≠ 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ O ∧
      (∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) ∧ (∀ y ∈ K, y ∉ Γ → fderiv ℝ f y (V y) < 0) ∧
      ∀ y, ‖V y‖ ≤ κ := by
  -- a fixed thickening of K inside O
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  set O₁ : Set E := thickening δ K with hO₁
  have hO₁o : IsOpen O₁ := isOpen_thickening
  have hO₁O : O₁ ⊆ O := (thickening_subset_cthickening δ K).trans hδO
  have hKO₁ : K ⊆ O₁ := self_subset_thickening hδ K
  have hf₁ : ContDiffOn ℝ 1 f O₁ := hf.mono hO₁O
  -- pseudo-gradients strict on the layers
  have hpg : ∀ k : ℕ, ∃ W : E → E, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ O₁ ∧
      (∀ y ∈ O₁, fderiv ℝ f y (W y) ≤ 0) ∧ ∀ y ∈ layer K Γ k, fderiv ℝ f y (W y) < 0 := by
    intro k
    have hA : IsCompact (layer K Γ k) :=
      hK.of_isClosed_subset (layer_isClosed hK.isClosed Γ k) inter_subset_left
    exact exists_pseudoGradient hO₁o hf₁ hA (fun x hx => hKO₁ hx.1)
      (fun x hx => hne x hx.1 (not_mem_of_mem_layer hx))
  choose W hWs hWc hWt hWle hWlt using hpg
  -- bounds for all iterated derivatives
  have hbd : ∀ k i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (W k) x‖ ≤ C := fun k i =>
    ((hWc k).iteratedFDeriv i).exists_bound_of_continuous
      ((hWs k).continuous_iteratedFDeriv (by exact_mod_cast le_top))
  choose C hC using hbd
  set S : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k + 1), |C k i| with hS
  have hS0 : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg fun i _ => abs_nonneg _
  set ε : ℕ → ℝ := fun k => κ / 2 / 2 ^ k / (1 + S k) with hε
  have hε0 : ∀ k, 0 < ε k := fun k => by
    have := hS0 k
    positivity
  have hεC : ∀ k i, i ≤ k → ε k * |C k i| ≤ κ / 2 / 2 ^ k := by
    intro k i hik
    have hle : |C k i| ≤ 1 + S k := by
      have h1 : |C k i| ≤ S k :=
        Finset.single_le_sum (f := fun i => |C k i|) (fun j _ => abs_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
      linarith
    have hpos : 0 < 1 + S k := by linarith [hS0 k]
    calc ε k * |C k i| = κ / 2 / 2 ^ k * (|C k i| / (1 + S k)) := by
          rw [hε]
          ring
      _ ≤ κ / 2 / 2 ^ k * 1 := by
          gcongr
          exact (div_le_one hpos).mpr hle
      _ = κ / 2 / 2 ^ k := mul_one _
  -- the terms of the series
  set g : ℕ → E → E := fun k x => ε k • W k x with hg
  have hgs : ∀ k, ContDiff ℝ ∞ (g k) := fun k => (hWs k).const_smul (ε k)
  have hgd : ∀ (i : ℕ) (k : ℕ) (x : E), ‖iteratedFDeriv ℝ i (g k) x‖ ≤ ε k * |C k i| := by
    intro i k x
    have e : g k = ε k • W k := rfl
    rw [e, iteratedFDeriv_const_smul_apply ((hWs k).contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_of_nonneg (hε0 k).le]
    exact mul_le_mul_of_nonneg_left ((hC k i x).trans (le_abs_self _)) (hε0 k).le
  have hsum : ∀ i : ℕ, Summable fun k => ε k * |C k i| := by
    intro i
    refine Summable.of_norm_bounded_eventually_nat (summable_geometric_two' κ) ?_
    filter_upwards [eventually_ge_atTop i] with k hk
    rw [Real.norm_of_nonneg (mul_nonneg (hε0 k).le (abs_nonneg _))]
    exact hεC k i hk
  have hgx : ∀ x, ∀ k, ‖g k x‖ ≤ κ / 2 / 2 ^ k := by
    intro x k
    have h := hgd 0 k x
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (hεC k 0 (Nat.zero_le k))
  have hgsum : ∀ x, Summable fun k => g k x := fun x =>
    Summable.of_norm_bounded (summable_geometric_two' κ) (hgx x)
  -- the sum
  refine ⟨fun x => ∑' k, g k x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_tsum (N := ⊤) hgs (fun i _ => hsum i) (fun i k x _ => hgd i k x)
  · -- compact support inside the closed thickening
    have hsupp : Function.support (fun x => ∑' k, g k x) ⊆ O₁ := by
      intro x hx
      by_contra hxO
      apply hx
      have h0 : ∀ k, g k x = 0 := by
        intro k
        have : x ∉ tsupport (W k) := fun h => hxO (hWt k h)
        change ε k • W k x = 0
        rw [image_eq_zero_of_notMem_tsupport this, smul_zero]
      simp [h0]
    have htsupp : tsupport (fun x => ∑' k, g k x) ⊆ cthickening δ K :=
      closure_minimal (hsupp.trans (thickening_subset_cthickening δ K)) isClosed_cthickening
    exact (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) htsupp
  · intro x hx
    have hsupp : Function.support (fun x => ∑' k, g k x) ⊆ O₁ := by
      intro x hx
      by_contra hxO
      apply hx
      have h0 : ∀ k, g k x = 0 := by
        intro k
        have : x ∉ tsupport (W k) := fun h => hxO (hWt k h)
        change ε k • W k x = 0
        rw [image_eq_zero_of_notMem_tsupport this, smul_zero]
      simp [h0]
    exact hδO (closure_minimal (hsupp.trans (thickening_subset_cthickening δ K))
      isClosed_cthickening hx)
  · intro y hy
    rw [ContinuousLinearMap.map_tsum _ (hgsum y)]
    refine tsum_nonpos fun k => ?_
    change fderiv ℝ f y (ε k • W k y) ≤ 0
    rw [map_smul, smul_eq_mul]
    by_cases hy₁ : y ∈ O₁
    · exact mul_nonpos_of_nonneg_of_nonpos (hε0 k).le (hWle k y hy₁)
    · have : y ∉ tsupport (W k) := fun h => hy₁ (hWt k h)
      rw [image_eq_zero_of_notMem_tsupport this, map_zero, mul_zero]
  · intro y hyK hyΓ
    obtain ⟨k₀, hk₀⟩ := exists_layer hΓ hyK hyΓ
    rw [ContinuousLinearMap.map_tsum _ (hgsum y)]
    have hterm : ∀ k, fderiv ℝ f y (g k y) ≤ 0 := by
      intro k
      change fderiv ℝ f y (ε k • W k y) ≤ 0
      rw [map_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (hε0 k).le (hWle k y (hKO₁ hyK))
    have hneg : fderiv ℝ f y (g k₀ y) < 0 := by
      change fderiv ℝ f y (ε k₀ • W k₀ y) < 0
      rw [map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg (hε0 k₀) (hWlt k₀ y hk₀)
    have hs : Summable fun k => -fderiv ℝ f y (g k y) := by
      refine Summable.of_norm_bounded
        ((summable_geometric_two' κ).mul_left ‖fderiv ℝ f y‖) fun k => ?_
      rw [norm_neg]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hgx y k) (norm_nonneg _))
    have hle := hs.le_tsum k₀ (fun k _ => neg_nonneg.mpr (hterm k))
    rw [tsum_neg] at hle
    linarith
  · intro y
    calc ‖∑' k, g k y‖ ≤ ∑' k, ‖g k y‖ :=
          norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (hgx y)
            (summable_geometric_two' κ))
      _ ≤ ∑' k : ℕ, κ / 2 / 2 ^ k :=
          (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (hgx y)
            (summable_geometric_two' κ)).tsum_le_tsum (hgx y) (summable_geometric_two' κ)
      _ = κ := tsum_geometric_two' κ

end

end Finsler.StrictField
