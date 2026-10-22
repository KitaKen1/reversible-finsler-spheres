module

public import Finsler.Algebra.JacobiPositive

/-! Positivity of a Jacobi operator on the families vanishing at the ends of chains. Let H be a
symmetric operator on the L² product of copies of V indexed by the residues modulo K whose
component at i is c (T_i w_{i+1} + A_i w_i + B_i w_{i-1}) with c > 0 and injective T_i, B_i,
and suppose the quadratic form of H is nonnegative on the families vanishing on a set S of
indices. A family u vanishing on S with zero form is annihilated by H outside S. If u vanishes
at the neighbours of a set C of indices which are not in C, the restriction of u to C has zero
form as well: the restriction and the rest are orthogonal for H, because H couples only
neighbours. If C is the chain e - 1, ..., e - (r - 1) and the indices e, e - 1, ...,
e - (r - 1) are outside S, the equation at e gives B_e u_{e-1} = 0, hence u_{e-1} = 0, and
inductively u vanishes on the chain; symmetrically for a chain e + 1, ..., e + (r - 1) with
the coefficients T. Hence the form of H is positive on the nonzero families vanishing on a set
S₂ containing S whose complement is covered by such chains with ends in S₂. This is the absence
of conjugate points on a minimizing chain of any length; for chains of one index it is the
statement of the positivity of the diagonal blocks. -/

@[expose] public section

namespace Finsler.ChainPositive

open Finsler.JacobiPositive
open scoped RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {K : ℕ} [NeZero K]

open Classical in
/-- The restriction of a family to a set of indices. -/
def restr (C : Set (ZMod K)) (u : PiLp 2 (fun _ : ZMod K => V)) : PiLp 2 (fun _ : ZMod K => V) :=
  WithLp.toLp 2 fun i => if i ∈ C then u i else 0

omit [InnerProductSpace ℝ V] [NeZero K] in
theorem restr_of_mem {C : Set (ZMod K)} (u : PiLp 2 (fun _ : ZMod K => V)) {i : ZMod K}
    (hi : i ∈ C) : restr C u i = u i := by
  classical
  exact ite_eq_left hi

omit [InnerProductSpace ℝ V] [NeZero K] in
theorem restr_of_not_mem {C : Set (ZMod K)} (u : PiLp 2 (fun _ : ZMod K => V)) {i : ZMod K}
    (hi : i ∉ C) : restr C u i = 0 := by
  classical
  exact ite_eq_right hi

omit [InnerProductSpace ℝ V] [NeZero K] in
theorem restr_eq_zero_of_eq_zero (C : Set (ZMod K)) {u : PiLp 2 (fun _ : ZMod K => V)}
    {i : ZMod K} (h : u i = 0) : restr C u i = 0 := by
  by_cases hi : i ∈ C
  · rw [restr_of_mem u hi, h]
  · exact restr_of_not_mem u hi

variable (H : PiLp 2 (fun _ : ZMod K => V) →ₗ[ℝ] PiLp 2 (fun _ : ZMod K => V))
  (T A B : ZMod K → V →ₗ[ℝ] V) {c : ℝ}
  (hJ : ∀ (w : PiLp 2 (fun _ : ZMod K => V)) (i : ZMod K),
    H w i = c • (T i (w (i + 1)) + A i (w i) + B i (w (i - 1))))
  (hH : H.IsSymmetric) (hc : 0 < c) (S : Set (ZMod K))
  (hpsd : ∀ z : PiLp 2 (fun _ : ZMod K => V), (∀ i ∈ S, z i = 0) → 0 ≤ ⟪H z, z⟫)

include hH hpsd in
/-- A family vanishing on S with zero form is annihilated by the operator outside S. -/
theorem apply_eq_zero {u : PiLp 2 (fun _ : ZMod K => V)} (hu : ∀ i ∈ S, u i = 0)
    (hzero : ⟪H u, u⟫ = 0) {j : ZMod K} (hj : j ∉ S) : H u j = 0 := by
  have hline : ∀ t : ℝ, 0 ≤ ⟪H (u + t • PiLp.single 2 j (H u j)),
      (u + t • PiLp.single 2 j (H u j) : PiLp 2 (fun _ : ZMod K => V))⟫ := by
    intro t
    refine hpsd _ fun l hl => ?_
    have hlj : l ≠ j := fun h => hj (h ▸ hl)
    change u l + t • (PiLp.single 2 j (H u j) : PiLp 2 (fun _ : ZMod K => V)) l = 0
    rw [hu l hl, PiLp.single_eq_of_ne 2 hlj, smul_zero, add_zero]
  have h := inner_eq_zero_of_nonneg H hH hline hzero
  rw [inner_single] at h
  exact inner_self_eq_zero.mp h

include hJ hH hpsd in
/-- If a family vanishing on S with zero form vanishes at the neighbours of a set C outside C,
its restriction to C has zero form. -/
theorem inner_restr_eq_zero (C : Set (ZMod K)) {u : PiLp 2 (fun _ : ZMod K => V)}
    (hu : ∀ i ∈ S, u i = 0) (hbd : ∀ i, i ∉ C → (i + 1 ∈ C ∨ i - 1 ∈ C) → u i = 0)
    (hzero : ⟪H u, u⟫ = 0) : ⟪H (restr C u), restr C u⟫ = 0 := by
  have hv : ∀ i ∈ S, restr C u i = 0 := fun i hi => restr_eq_zero_of_eq_zero C (hu i hi)
  have hv' : ∀ i ∈ S, (u - restr C u) i = 0 := fun i hi => by
    change u i - restr C u i = 0
    rw [hu i hi, hv i hi, sub_zero]
  have h0 := hpsd _ hv
  have h0' := hpsd _ hv'
  have hcross : ⟪H (restr C u), u - restr C u⟫ = 0 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    change ⟪H (restr C u) i, u i - restr C u i⟫ = 0
    by_cases hi : i ∈ C
    · rw [restr_of_mem u hi, sub_self, inner_zero_right]
    · by_cases hn : i + 1 ∈ C ∨ i - 1 ∈ C
      · rw [hbd i hi hn, restr_of_not_mem u hi, sub_zero, inner_zero_right]
      · have h1 : i + 1 ∉ C := fun h => hn (Or.inl h)
        have h2 : i - 1 ∉ C := fun h => hn (Or.inr h)
        rw [hJ, restr_of_not_mem u hi, restr_of_not_mem u h1, restr_of_not_mem u h2, map_zero,
          map_zero, map_zero, add_zero, add_zero, smul_zero, inner_zero_left]
  have hsplit : ⟪H u, u⟫ = ⟪H (restr C u), restr C u⟫ +
      ⟪H (u - restr C u), u - restr C u⟫ := by
    have hsym : ⟪H (u - restr C u), restr C u⟫ = ⟪H (restr C u), u - restr C u⟫ := by
      rw [hH (u - restr C u) (restr C u), real_inner_comm]
    have e : u = restr C u + (u - restr C u) := by abel
    conv_lhs => rw [e]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym, hcross]
    ring
  linarith

variable (hB : ∀ i, Function.Injective (B i)) (hT : ∀ i, Function.Injective (T i))

include hJ hH hc hpsd hB in
/-- **A chain ending at e.** A family with zero form which vanishes on S and at e and e - r
vanishes at e - 1, ..., e - (r - 1), if the indices e, e - 1, ..., e - (r - 1) are outside
S. -/
theorem chain_back (e : ZMod K) (r : ℕ) (hr : r < K)
    (hS : ∀ t : ℕ, t < r → e - (t : ZMod K) ∉ S) {u : PiLp 2 (fun _ : ZMod K => V)}
    (hu : ∀ i ∈ S, u i = 0) (hue : u e = 0) (hur : u (e - (r : ZMod K)) = 0)
    (hzero : ⟪H u, u⟫ = 0) : ∀ s : ℕ, s < r → u (e - (s : ZMod K)) = 0 := by
  set C : Set (ZMod K) := {i | ∃ s : ℕ, 1 ≤ s ∧ s < r ∧ i = e - (s : ZMod K)} with hC
  have hbd : ∀ i, i ∉ C → (i + 1 ∈ C ∨ i - 1 ∈ C) → u i = 0 := by
    rintro i hi (⟨s, hs1, hsr, hs⟩ | ⟨s, hs1, hsr, hs⟩)
    · have hi' : i = e - ((s + 1 : ℕ) : ZMod K) := by
        rw [Nat.cast_add, Nat.cast_one, ← sub_sub, ← hs, add_sub_cancel_right]
      by_cases hlt : s + 1 < r
      · exact absurd ⟨s + 1, by omega, hlt, hi'⟩ hi
      · have hr' : s + 1 = r := by omega
        rw [hi', hr']
        exact hur
    · have hi' : i = e - ((s - 1 : ℕ) : ZMod K) := by
        rw [Nat.cast_sub hs1, Nat.cast_one, ← sub_add, ← hs, sub_add_cancel]
      by_cases h1 : 1 ≤ s - 1
      · exact absurd ⟨s - 1, h1, by omega, hi'⟩ hi
      · have h0 : s - 1 = 0 := by omega
        rw [hi', h0, Nat.cast_zero, sub_zero]
        exact hue
  have hvz := inner_restr_eq_zero H T A B hJ hH S hpsd C hu hbd hzero
  have hvS : ∀ i ∈ S, restr C u i = 0 := fun i hi => restr_eq_zero_of_eq_zero C (hu i hi)
  have he1 : e + 1 ∉ C := by
    rintro ⟨s, hs1, hsr, hs⟩
    have h0 : ((s + 1 : ℕ) : ZMod K) = 0 := by
      rw [Nat.cast_add, Nat.cast_one]
      have h' : (s : ZMod K) + 1 = e - (e + 1) + 1 := by rw [hs]; ring
      rw [h']
      ring
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by omega) h0
    omega
  have hv : ∀ s : ℕ, s < r → restr C u (e - (s : ZMod K)) = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0, Nat.cast_zero, sub_zero]
        exact restr_eq_zero_of_eq_zero C hue
      · have hj : e - ((s - 1 : ℕ) : ZMod K) ∉ S := hS (s - 1) (by omega)
        have heq := apply_eq_zero H hH S hpsd hvS hvz hj
        rw [hJ] at heq
        have hmid : restr C u (e - ((s - 1 : ℕ) : ZMod K)) = 0 := ih (s - 1) (by omega) (by omega)
        have hnext : restr C u (e - ((s - 1 : ℕ) : ZMod K) + 1) = 0 := by
          rcases Nat.eq_or_lt_of_le hpos with h1 | h2
          · rw [← h1, Nat.sub_self, Nat.cast_zero, sub_zero]
            exact restr_of_not_mem u he1
          · have e2 : e - ((s - 1 : ℕ) : ZMod K) + 1 = e - ((s - 2 : ℕ) : ZMod K) := by
              rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_sub (by omega : 2 ≤ s)]
              push_cast
              ring
            rw [e2]
            exact ih (s - 2) (by omega) (by omega)
        have hprev : e - ((s - 1 : ℕ) : ZMod K) - 1 = e - (s : ZMod K) := by
          rw [Nat.cast_sub (by omega : 1 ≤ s)]
          push_cast
          ring
        rw [hmid, hnext, hprev, map_zero, map_zero, zero_add, zero_add] at heq
        have h3 : B (e - ((s - 1 : ℕ) : ZMod K)) (restr C u (e - (s : ZMod K))) = 0 :=
          (smul_eq_zero.mp heq).resolve_left hc.ne'
        exact hB _ (h3.trans (map_zero _).symm)
  intro s hs
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · rw [h0, Nat.cast_zero, sub_zero]
    exact hue
  · have hmem : e - (s : ZMod K) ∈ C := ⟨s, hpos, hs, rfl⟩
    rw [← restr_of_mem u hmem]
    exact hv s hs

include hJ hH hc hpsd hT in
/-- **A chain starting at e.** A family with zero form which vanishes on S and at e and e + r
vanishes at e + 1, ..., e + (r - 1), if the indices e, e + 1, ..., e + (r - 1) are outside
S. -/
theorem chain_fwd (e : ZMod K) (r : ℕ) (hr : r < K)
    (hS : ∀ t : ℕ, t < r → e + (t : ZMod K) ∉ S) {u : PiLp 2 (fun _ : ZMod K => V)}
    (hu : ∀ i ∈ S, u i = 0) (hue : u e = 0) (hur : u (e + (r : ZMod K)) = 0)
    (hzero : ⟪H u, u⟫ = 0) : ∀ s : ℕ, s < r → u (e + (s : ZMod K)) = 0 := by
  set C : Set (ZMod K) := {i | ∃ s : ℕ, 1 ≤ s ∧ s < r ∧ i = e + (s : ZMod K)} with hC
  have hbd : ∀ i, i ∉ C → (i + 1 ∈ C ∨ i - 1 ∈ C) → u i = 0 := by
    rintro i hi (⟨s, hs1, hsr, hs⟩ | ⟨s, hs1, hsr, hs⟩)
    · have hi' : i = e + ((s - 1 : ℕ) : ZMod K) := by
        rw [Nat.cast_sub hs1, Nat.cast_one, ← add_sub_assoc, ← hs, add_sub_cancel_right]
      by_cases h1 : 1 ≤ s - 1
      · exact absurd ⟨s - 1, h1, by omega, hi'⟩ hi
      · have h0 : s - 1 = 0 := by omega
        rw [hi', h0, Nat.cast_zero, add_zero]
        exact hue
    · have hi' : i = e + ((s + 1 : ℕ) : ZMod K) := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← hs, sub_add_cancel]
      by_cases hlt : s + 1 < r
      · exact absurd ⟨s + 1, by omega, hlt, hi'⟩ hi
      · have hr' : s + 1 = r := by omega
        rw [hi', hr']
        exact hur
  have hvz := inner_restr_eq_zero H T A B hJ hH S hpsd C hu hbd hzero
  have hvS : ∀ i ∈ S, restr C u i = 0 := fun i hi => restr_eq_zero_of_eq_zero C (hu i hi)
  have he1 : e - 1 ∉ C := by
    rintro ⟨s, hs1, hsr, hs⟩
    have h0 : ((s + 1 : ℕ) : ZMod K) = 0 := by
      rw [Nat.cast_add, Nat.cast_one]
      have h' : (s : ZMod K) + 1 = e - 1 - e + 1 := by rw [hs]; ring
      rw [h']
      ring
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by omega) h0
    omega
  have hv : ∀ s : ℕ, s < r → restr C u (e + (s : ZMod K)) = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0, Nat.cast_zero, add_zero]
        exact restr_eq_zero_of_eq_zero C hue
      · have hj : e + ((s - 1 : ℕ) : ZMod K) ∉ S := hS (s - 1) (by omega)
        have heq := apply_eq_zero H hH S hpsd hvS hvz hj
        rw [hJ] at heq
        have hmid : restr C u (e + ((s - 1 : ℕ) : ZMod K)) = 0 := ih (s - 1) (by omega) (by omega)
        have hprev : restr C u (e + ((s - 1 : ℕ) : ZMod K) - 1) = 0 := by
          rcases Nat.eq_or_lt_of_le hpos with h1 | h2
          · rw [← h1, Nat.sub_self, Nat.cast_zero, add_zero]
            exact restr_of_not_mem u he1
          · have e2 : e + ((s - 1 : ℕ) : ZMod K) - 1 = e + ((s - 2 : ℕ) : ZMod K) := by
              rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_sub (by omega : 2 ≤ s)]
              push_cast
              ring
            rw [e2]
            exact ih (s - 2) (by omega) (by omega)
        have hnext : e + ((s - 1 : ℕ) : ZMod K) + 1 = e + (s : ZMod K) := by
          rw [Nat.cast_sub (by omega : 1 ≤ s)]
          push_cast
          ring
        rw [hmid, hprev, hnext, map_zero, map_zero, add_zero, add_zero] at heq
        have h3 : T (e + ((s - 1 : ℕ) : ZMod K)) (restr C u (e + (s : ZMod K))) = 0 :=
          (smul_eq_zero.mp heq).resolve_left hc.ne'
        exact hT _ (h3.trans (map_zero _).symm)
  intro s hs
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · rw [h0, Nat.cast_zero, add_zero]
    exact hue
  · have hmem : e + (s : ZMod K) ∈ C := ⟨s, hpos, hs, rfl⟩
    rw [← restr_of_mem u hmem]
    exact hv s hs

include hJ hH hc hpsd hB hT in
/-- **Positivity on the families vanishing at the ends of chains.** Let S₂ contain S, and
suppose every index outside S₂ lies on a chain e - s (or e + s) with 0 < s < r whose ends e and
e - r (or e + r) are in S₂ and whose indices e - t (or e + t), t < r, are outside S. Then the
form is positive on the nonzero families vanishing on S₂. -/
theorem inner_pos (S₂ : Set (ZMod K)) (hSS : S ⊆ S₂)
    (hchain : ∀ i, i ∉ S₂ → ∃ (e : ZMod K) (r s : ℕ), s < r ∧ r < K ∧ e ∈ S₂ ∧
      ((i = e - (s : ZMod K) ∧ e - (r : ZMod K) ∈ S₂ ∧ ∀ t : ℕ, t < r → e - (t : ZMod K) ∉ S) ∨
        (i = e + (s : ZMod K) ∧ e + (r : ZMod K) ∈ S₂ ∧
          ∀ t : ℕ, t < r → e + (t : ZMod K) ∉ S)))
    {u : PiLp 2 (fun _ : ZMod K => V)} (hu : ∀ i ∈ S₂, u i = 0) (hne : u ≠ 0) :
    0 < ⟪H u, u⟫ := by
  have hu' : ∀ i ∈ S, u i = 0 := fun i hi => hu i (hSS hi)
  refine lt_of_le_of_ne (hpsd u hu') fun hzero => hne ?_
  refine PiLp.ext fun i => ?_
  by_cases hi : i ∈ S₂
  · exact hu i hi
  · obtain ⟨e, r, s, hs, hr, he, h | h⟩ := hchain i hi
    · obtain ⟨rfl, her, hS⟩ := h
      exact chain_back H T A B hJ hH hc S hpsd hB e r hr hS hu' (hu e he) (hu _ her)
        hzero.symm s hs
    · obtain ⟨rfl, her, hS⟩ := h
      exact chain_fwd H T A B hJ hH hc S hpsd hT e r hr hS hu' (hu e he) (hu _ her)
        hzero.symm s hs

end

end Finsler.ChainPositive
