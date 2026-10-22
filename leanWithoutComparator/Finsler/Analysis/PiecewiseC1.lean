module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! Gluing N curves on the equal pieces [k/N, (k+1)/N] of [0,1]. The glued curve evaluates the k-th
curve at the local parameter Nt − k, with the last piece closed at t = 1; its velocity is N times
the velocity of the piece. When the pieces are C¹ on [0,1] and match at the ends, the glued curve is
continuous on [0,1] and is the primitive of its velocity (fundamental theorem of calculus off the
countable set of break points), integrals over [0,1] of functions given by the pieces split into
the averages of the piece integrals, and sup bounds on the pieces transfer to the glued curve. -/

@[expose] public section

namespace Finsler.PiecewiseC1

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The piece of t among N equal pieces of [0,1]. -/
def pieceIdx (N : ℕ) (t : ℝ) : ℕ := min ⌊(N : ℝ) * t⌋₊ (N - 1)

/-- The local parameter of t in its piece. -/
def pieceLoc (N : ℕ) (t : ℝ) : ℝ := (N : ℝ) * t - (pieceIdx N t : ℝ)

theorem pieceIdx_lt {N : ℕ} (hN : 0 < N) (t : ℝ) : pieceIdx N t < N :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN one_pos)

theorem natCast_pred {N : ℕ} (hN : 0 < N) : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne'), Nat.cast_one]

theorem pieceIdx_eq {N k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N)) : pieceIdx N t = k := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have h1 : (k : ℝ) ≤ N * t := by
    have := ht.1
    rw [div_le_iff₀ hN] at this
    linarith
  have h2 : (N : ℝ) * t < k + 1 := by
    have := ht.2
    rw [lt_div_iff₀ hN] at this
    linarith
  have hf : ⌊(N : ℝ) * t⌋₊ = k :=
    (Nat.floor_eq_iff ((Nat.cast_nonneg k).trans h1)).mpr ⟨h1, h2⟩
  unfold pieceIdx
  rw [hf]
  exact min_eq_left (Nat.le_sub_one_of_lt hk)

theorem pieceIdx_one (N : ℕ) : pieceIdx N 1 = N - 1 := by
  unfold pieceIdx
  rw [mul_one, Nat.floor_natCast]
  exact min_eq_right (Nat.sub_le N 1)

/-- The local parameter of a point of [0,1] lies in [0,1]. -/
theorem pieceLoc_mem {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pieceLoc N t ∈ Icc (0 : ℝ) 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNt : 0 ≤ (N : ℝ) * t := mul_nonneg hN'.le ht.1
  unfold pieceLoc pieceIdx
  rcases le_total ⌊(N : ℝ) * t⌋₊ (N - 1) with h | h
  · rw [min_eq_left h]
    exact ⟨sub_nonneg.mpr (Nat.floor_le hNt),
      by linarith [Nat.lt_floor_add_one ((N : ℝ) * t)]⟩
  · rw [min_eq_right h, natCast_pred hN]
    have h1 : ((N - 1 : ℕ) : ℝ) ≤ ⌊(N : ℝ) * t⌋₊ := by exact_mod_cast h
    rw [natCast_pred hN] at h1
    have h2 := Nat.floor_le hNt
    have h3 : (N : ℝ) * t ≤ N := by nlinarith [ht.2]
    constructor <;> nlinarith

/-- The point t lies in the closed piece of its index. -/
theorem mem_piece {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ∈ Icc ((pieceIdx N t : ℝ) / N) (((pieceIdx N t : ℝ) + 1) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := pieceLoc_mem hN ht
  unfold pieceLoc at h
  constructor
  · rw [div_le_iff₀ hN']
    linarith [h.1]
  · rw [le_div_iff₀ hN']
    linarith [h.2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The glued curve. -/
def glue (N : ℕ) (γ : ℕ → ℝ → E) (t : ℝ) : E := γ (pieceIdx N t) (pieceLoc N t)

/-- The glued velocity. -/
def glueVel (N : ℕ) (γ' : ℕ → ℝ → E) (t : ℝ) : E := (N : ℝ) • γ' (pieceIdx N t) (pieceLoc N t)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glue_eq_of_mem_Ico {N k : ℕ} (hk : k < N) (γ : ℕ → ℝ → E) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N)) : glue N γ t = γ k ((N : ℝ) * t - k) := by
  unfold glue pieceLoc
  rw [pieceIdx_eq hk ht]

theorem glueVel_eq_of_mem_Ico {N k : ℕ} (hk : k < N) (γ' : ℕ → ℝ → E) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :
    glueVel N γ' t = (N : ℝ) • γ' k ((N : ℝ) * t - k) := by
  unfold glueVel pieceLoc
  rw [pieceIdx_eq hk ht]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- With matching ends the glued curve is the k-th curve on the whole closed piece. -/
theorem glue_eq_of_mem_Icc {N k : ℕ} (hk : k < N) {γ : ℕ → ℝ → E}
    (hmatch : ∀ j, j + 1 < N → γ j 1 = γ (j + 1) 0) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) : glue N γ t = γ k ((N : ℝ) * t - k) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  rcases eq_or_lt_of_le ht.2 with he | hlt
  · have hNt : (N : ℝ) * t - k = 1 := by
      rw [he]
      field_simp
      ring
    rw [hNt]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk1 | hk1
    · -- the next piece starts at t
      have hmem : t ∈ Ico (((k + 1 : ℕ) : ℝ) / N) ((((k + 1 : ℕ) : ℝ) + 1) / N) := by
        rw [he]
        push_cast
        constructor
        · exact le_rfl
        · apply div_lt_div_of_pos_right _ hN
          linarith
      rw [glue_eq_of_mem_Ico hk1 γ hmem, hmatch k hk1]
      congr 1
      rw [he]
      push_cast
      field_simp
      ring
    · -- the last piece, t = 1
      have hk' : k = N - 1 := by omega
      have ht1 : t = 1 := by
        rw [he]
        have : ((k : ℝ) + 1) = N := by exact_mod_cast hk1
        rw [this, div_self hN.ne']
      unfold glue pieceLoc
      rw [ht1, pieceIdx_one N, ← hk']
      congr 1
      rw [mul_one]
      have : ((k : ℝ) + 1) = N := by exact_mod_cast hk1
      linarith
  · exact glue_eq_of_mem_Ico hk γ ⟨ht.1, hlt⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem affine_mapsTo {N k : ℕ} (hN : (0 : ℝ) < N) :
    MapsTo (fun t : ℝ => (N : ℝ) * t - k) (Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) (Icc 0 1) := by
  intro t ht
  constructor
  · have := ht.1
    rw [div_le_iff₀ hN] at this
    simp only
    linarith
  · have := ht.2
    rw [le_div_iff₀ hN] at this
    simp only
    linarith

/-- The break points. -/
def breaks (N : ℕ) : Set ℝ := range (fun k : ℕ => (k : ℝ) / N)

theorem breaks_countable (N : ℕ) : (breaks N).Countable := countable_range _

section Glue

variable {N : ℕ} (hN : 0 < N) {γ γ' : ℕ → ℝ → E}
  (hγc : ∀ k < N, ContinuousOn (γ k) (Icc 0 1))
  (hγd : ∀ k < N, ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (γ k) (γ' k s) s)
  (hγc' : ∀ k < N, ContinuousOn (γ' k) (Icc 0 1))
  (hmatch : ∀ j, j + 1 < N → γ j 1 = γ (j + 1) 0)

omit [NormedSpace ℝ E] in
include hN hγc hmatch in
theorem glue_continuousOn : ContinuousOn (glue N γ) (Icc 0 1) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  let S : Fin N → Set ℝ := fun k => Icc (((k : ℕ) : ℝ) / N) ((((k : ℕ) : ℝ) + 1) / N)
  have hcont : ∀ k : Fin N, ContinuousOn (glue N γ) (S k) := by
    intro k
    have h1 : ContinuousOn (fun t : ℝ => γ k ((N : ℝ) * t - ((k : ℕ) : ℝ))) (S k) :=
      (hγc k k.2).comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
        (affine_mapsTo hN')
    exact h1.congr (fun t ht => glue_eq_of_mem_Icc k.2 hmatch ht)
  have hU := (locallyFinite_of_finite S).continuousOn_iUnion (fun _ => isClosed_Icc) hcont
  apply hU.mono
  intro t ht
  rw [mem_iUnion]
  exact ⟨⟨pieceIdx N t, pieceIdx_lt hN t⟩, mem_piece hN ht⟩

include hN hγd in
theorem glue_hasDerivAt {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1 \ breaks N) :
    HasDerivAt (glue N γ) (glueVel N γ' t) t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk := pieceIdx_lt hN t
  have hpiece := mem_piece hN (Ioo_subset_Icc_self ht.1)
  have hne1 : t ≠ (pieceIdx N t : ℝ) / N := fun h => ht.2 ⟨pieceIdx N t, h.symm⟩
  have hne2 : t ≠ ((pieceIdx N t : ℝ) + 1) / N := fun h =>
    ht.2 ⟨pieceIdx N t + 1, by push_cast; exact h.symm⟩
  have hopen : t ∈ Ioo ((pieceIdx N t : ℝ) / N) (((pieceIdx N t : ℝ) + 1) / N) :=
    ⟨lt_of_le_of_ne hpiece.1 (Ne.symm hne1), lt_of_le_of_ne hpiece.2 hne2⟩
  have hev : glue N γ =ᶠ[𝓝 t] fun s => γ (pieceIdx N t) ((N : ℝ) * s - (pieceIdx N t : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hopen.1 hopen.2] with s hs
    exact glue_eq_of_mem_Ico hk γ ⟨hs.1.le, hs.2⟩
  have hloc : (N : ℝ) * t - (pieceIdx N t : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    have h1 := hopen.1
    have h2 := hopen.2
    rw [div_lt_iff₀ hN'] at h1
    rw [lt_div_iff₀ hN'] at h2
    constructor <;> linarith
  have h1 : HasDerivAt (fun s : ℝ => (N : ℝ) * s - (pieceIdx N t : ℝ)) (N : ℝ) t := by
    simpa using ((hasDerivAt_id t).const_mul (N : ℝ)).sub_const (pieceIdx N t : ℝ)
  have hd := (hγd _ hk _ hloc).scomp t h1
  have hv : glueVel N γ' t = (N : ℝ) • γ' (pieceIdx N t) ((N : ℝ) * t - (pieceIdx N t : ℝ)) :=
    glueVel_eq_of_mem_Ico hk γ' ⟨hopen.1.le, hopen.2⟩
  rw [hv]
  exact hd.congr_of_eventuallyEq hev

include hN hγc' in
theorem glueVel_intervalIntegrable : IntervalIntegrable (glueVel N γ') volume 0 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := IntervalIntegrable.trans_iterate (a := fun k : ℕ => (k : ℝ) / N) (n := N)
    (f := glueVel N γ') (μ := volume) ?_
  · simpa [div_self hN'.ne'] using h
  intro k hk
  have hle : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
    apply div_le_div_of_nonneg_right _ hN'.le
    push_cast
    linarith
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
  have hc : ContinuousOn (fun t : ℝ => (N : ℝ) • γ' k ((N : ℝ) * t - k))
      (Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :=
    continuousOn_const.smul ((hγc' k hk).comp
      ((continuous_const.mul continuous_id).sub continuous_const).continuousOn (affine_mapsTo hN'))
  have hI : IntegrableOn (fun t : ℝ => (N : ℝ) • γ' k ((N : ℝ) * t - k))
      (Ioo ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) := by
    push_cast
    exact (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  apply hI.congr_fun _ measurableSet_Ioo
  intro t ht
  push_cast at ht
  exact (glueVel_eq_of_mem_Ico hk γ' ⟨ht.1.le, ht.2⟩).symm

variable [CompleteSpace E]

include hN hγc hγd hγc' hmatch in
/-- The glued curve is the primitive of its velocity on [0,1]. -/
theorem glue_eq_add_integral {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    glue N γ t = glue N γ 0 + ∫ s in (0 : ℝ)..t, glueVel N γ' s := by
  have h := integral_eq_of_hasDerivAt_off_countable_of_le (glue N γ) (glueVel N γ') ht.1
    (breaks_countable N) ((glue_continuousOn hN hγc hmatch).mono (Icc_subset_Icc le_rfl ht.2))
    (fun x hx => glue_hasDerivAt hN hγd ⟨⟨hx.1.1, hx.1.2.trans_le ht.2⟩, hx.2⟩)
    ((glueVel_intervalIntegrable hN hγc').mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl ht.2))
  rw [h]
  abel

end Glue

omit [NormedSpace ℝ E] in
/-- Sup bounds on the pieces transfer to the glued curve. -/
theorem norm_glue_sub_le {N : ℕ} (hN : 0 < N) {γ η : ℕ → ℝ → E} {ε : ℝ}
    (h : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1, ‖γ k s - η k s‖ ≤ ε) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖glue N γ t - glue N η t‖ ≤ ε :=
  h _ (pieceIdx_lt hN t) _ (pieceLoc_mem hN ht)

theorem norm_glueVel_sub_le {N : ℕ} (hN : 0 < N) {γ' η' : ℕ → ℝ → E} {ε : ℝ}
    (h : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1, ‖γ' k s - η' k s‖ ≤ ε) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖glueVel N γ' t - glueVel N η' t‖ ≤ N * ε := by
  unfold glueVel
  rw [← smul_sub, norm_smul, Real.norm_natCast]
  exact mul_le_mul_of_nonneg_left (h _ (pieceIdx_lt hN t) _ (pieceLoc_mem hN ht))
    (Nat.cast_nonneg _)

/-- A bound for the glued velocity. -/
theorem norm_glueVel_le {N : ℕ} (hN : 0 < N) {γ' : ℕ → ℝ → E} {C : ℝ}
    (h : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1, ‖γ' k s‖ ≤ C) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖glueVel N γ' t‖ ≤ N * C := by
  unfold glueVel
  rw [norm_smul, Real.norm_natCast]
  exact mul_le_mul_of_nonneg_left (h _ (pieceIdx_lt hN t) _ (pieceLoc_mem hN ht))
    (Nat.cast_nonneg _)

/-- Integrals of functions given by the pieces split into the averages of the piece integrals. -/
theorem integral_piecewise {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ}
    (hN : 0 < N) {f : ℝ → F} {φ : ℕ → ℝ → F}
    (hφ : ∀ k < N, ContinuousOn (φ k) (Icc 0 1))
    (hf : ∀ k < N, ∀ t ∈ Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N), f t = φ k ((N : ℝ) * t - k)) :
    ∫ t in (0 : ℝ)..1, f t = ∑ k ∈ Finset.range N, (N : ℝ)⁻¹ • ∫ s in (0 : ℝ)..1, φ k s := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpiece : ∀ k < N, IntervalIntegrable f volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) ∧
      ∫ t in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), f t = (N : ℝ)⁻¹ • ∫ s in (0 : ℝ)..1, φ k s := by
    intro k hk
    have hle : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hN'.le
      push_cast
      linarith
    have hc : ContinuousOn (fun t : ℝ => φ k ((N : ℝ) * t - k))
        (Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :=
      (hφ k hk).comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
        (affine_mapsTo hN')
    have heq : ∀ t ∈ Ioo ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N), f t = φ k ((N : ℝ) * t - k) := by
      intro t ht
      push_cast at ht
      exact hf k hk t ht
    constructor
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
      have hI : IntegrableOn (fun t : ℝ => φ k ((N : ℝ) * t - k))
          (Ioo ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) := by
        push_cast
        exact (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
      exact hI.congr_fun (fun t ht => (heq t ht).symm) measurableSet_Ioo
    · have h1 : ∫ t in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), f t =
          ∫ t in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), φ k ((N : ℝ) * t - k) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) / N := by
          rw [ae_iff]
          simp
        filter_upwards [hne] with t ht1 ht2
        rw [uIoc_of_le hle] at ht2
        exact heq t ⟨ht2.1, lt_of_le_of_ne ht2.2 ht1⟩
      rw [h1, intervalIntegral.integral_comp_mul_sub (fun t => φ k t) hN'.ne']
      congr 1
      have e1 : (N : ℝ) * ((k : ℝ) / N) - k = 0 := by
        field_simp
        ring
      have e2 : (N : ℝ) * (((k + 1 : ℕ) : ℝ) / N) - k = 1 := by
        push_cast
        field_simp
        ring
      rw [e1, e2]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / N)
    (n := N) (f := f) (μ := volume) (fun k hk => (hpiece k hk).1)
  simp only [Nat.cast_zero, zero_div, div_self hN'.ne'] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  exact (hpiece k (Finset.mem_range.mp hk)).2

end

end Finsler.PiecewiseC1
