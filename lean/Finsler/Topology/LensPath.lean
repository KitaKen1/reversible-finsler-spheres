module

public import Finsler.Topology.LensContinuation

/-! Invariance of lens pairs along a segment of functions. Let g and β be continuous functions
on a space, β bounded, and let a semiflow be a descent for g and for g + β; then it is a
descent for every g + s β, 0 ≤ s ≤ 1. Let 𝒲 be an open set, a, b cuts, δ > 0 and T, τ ≥ 0 times
such that for every s ∈ [0, 1] the flow takes the sublevels of b + δ and a + δ of g + s β below
b − δ and a − δ in time τ, and the points of 𝒲 below b + δ which are not taken below a − δ in
time T stay in 𝒲 as long as they are not taken below a − δ. Then the lens pairs in 𝒲 of g and
of g + β have isomorphic cohomology: the segment is divided into steps on which the function
changes by at most δ, and the invariance under small changes applies to each step. -/

@[expose] public section

namespace Finsler.LensPath

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {g β : W → ℝ} (D : Descent W g)

/-- The function g + s β. -/
def along (g β : W → ℝ) (s : ℝ) : W → ℝ := fun w => g w + s * β w

theorem along_continuous (hg : Continuous g) (hβ : Continuous β) (s : ℝ) :
    Continuous (along g β s) := hg.add (continuous_const.mul hβ)

/-- A descent for g and for g + β is a descent for g + s β, 0 ≤ s ≤ 1. -/
theorem along_mono (h₁ : ∀ t w, 0 ≤ t → g (D.flow t w) + β (D.flow t w) ≤ g w + β w) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) (w : W) (ht : 0 ≤ t) :
    along g β s (D.flow t w) ≤ along g β s w := by
  have e1 := mul_le_mul_of_nonneg_left (D.mono t w ht) (sub_nonneg.mpr hs1)
  have e2 := mul_le_mul_of_nonneg_left (h₁ t w ht) hs0
  unfold along
  nlinarith

/-- Two functions of the segment whose parameters differ by at most δ / M differ by at most
δ, if |β| ≤ M. -/
theorem along_sub_le {M : ℝ} (hM : ∀ w, |β w| ≤ M) {s s' δ : ℝ} (hss : |s' - s| * M ≤ δ)
    (w : W) : along g β s' w ≤ along g β s w + δ := by
  have h1 : (s' - s) * β w ≤ |s' - s| * M :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left (hM w) (abs_nonneg _)))
  unfold along
  nlinarith

section Main

variable {𝒲 : Set W} {a b T τ δ M : ℝ}
  (h₁ : ∀ t w, 0 ≤ t → g (D.flow t w) + β (D.flow t w) ≤ g w + β w)
  (hg : Continuous g) (hβ : Continuous β) (hM : ∀ w, |β w| ≤ M) (h𝒲 : IsOpen 𝒲)
  (hδ : 0 < δ) (hT : 0 ≤ T) (hτ : 0 ≤ τ)
  (hpb : ∀ s, 0 ≤ s → s ≤ 1 → ∀ w, along g β s w < b + δ →
    along g β s (D.flow τ w) < b - δ)
  (hpa : ∀ s, 0 ≤ s → s ≤ 1 → ∀ w, along g β s w < a + δ →
    along g β s (D.flow τ w) < a - δ)
  (htrap : ∀ s, 0 ≤ s → s ≤ 1 → ∀ w, w ∈ 𝒲 → along g β s w < b + δ →
    a - δ ≤ along g β s (D.flow T w) → ∀ r, 0 ≤ r →
    a - δ ≤ along g β s (D.flow T (D.flow r w)) → D.flow r w ∈ 𝒲)

include hg hβ hM h𝒲 hδ hT hτ hpb hpa htrap in
/-- One step of the segment: the lens pairs in 𝒲 of g + s β and g + s' β have isomorphic
cohomology if |s' − s| M ≤ δ. -/
theorem nonempty_step {s s' : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs0' : 0 ≤ s') (hs1' : s' ≤ 1)
    (hss : |s' - s| * M ≤ δ) (n : ℕ) :
    Nonempty (H (triv (pairOf (partY_sub_partU (along g β s)
        (retarget D (along_mono D h₁ hs0 hs1)) 𝒲 a b T))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU (along g β s')
        (retarget D (along_mono D h₁ hs0' hs1')) 𝒲 a b T))) n) := by
  have hss' : |s - s'| * M ≤ δ := by rwa [abs_sub_comm]
  exact ⟨continuationEquiv (g₀ := along g β s) (g₁ := along g β s')
    (retarget D (along_mono D h₁ hs0 hs1)) (along_mono D h₁ hs0' hs1')
    (along_sub_le hM hss) (along_sub_le hM hss') hδ.le hT hτ (hpb s hs0 hs1) (hpa s hs0 hs1)
    (htrap s hs0 hs1) (along_continuous hg hβ s) (along_continuous hg hβ s') h𝒲 n⟩

include hg hβ hM h𝒲 hδ hT hτ hpb hpa htrap in
/-- The lens pairs in 𝒲 of g + 0 β and g + (i / N) β have isomorphic cohomology, for i ≤ N and
M ≤ N δ. -/
theorem nonempty_steps {N : ℕ} (hN : 0 < N) (hMN : M ≤ N * δ) (n : ℕ) :
    ∀ i : ℕ, ∀ hi : i ≤ N,
      Nonempty (H (triv (pairOf (partY_sub_partU (along g β 0)
          (retarget D (along_mono D h₁ le_rfl zero_le_one)) 𝒲 a b T))) n ≃ₗ[ZMod 2]
        H (triv (pairOf (partY_sub_partU (along g β ((i : ℝ) / N))
          (retarget D (along_mono D h₁ (div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg N))
            ((div_le_one (Nat.cast_pos.mpr hN)).mpr (Nat.cast_le.mpr hi)))) 𝒲 a b T))) n)
  | 0, _ => by
    have h := nonempty_step D h₁ hg hβ hM h𝒲 hδ hT hτ hpb hpa htrap (s := 0)
      (s' := ((0 : ℕ) : ℝ) / N) le_rfl zero_le_one
      (div_nonneg (Nat.cast_nonneg 0) (Nat.cast_nonneg N))
      ((div_le_one (Nat.cast_pos.mpr hN)).mpr (Nat.cast_le.mpr (Nat.zero_le N)))
      (by
        rw [Nat.cast_zero, zero_div, sub_self, abs_zero, zero_mul]
        exact hδ.le) n
    exact h
  | i + 1, hi => by
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    obtain ⟨e⟩ := nonempty_steps hN hMN n i (Nat.le_of_succ_le hi)
    obtain ⟨e'⟩ := nonempty_step D h₁ hg hβ hM h𝒲 hδ hT hτ hpb hpa htrap
      (s := (i : ℝ) / N) (s' := ((i + 1 : ℕ) : ℝ) / N)
      (div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg N))
      ((div_le_one hN').mpr (Nat.cast_le.mpr (Nat.le_of_succ_le hi)))
      (div_nonneg (Nat.cast_nonneg (i + 1)) (Nat.cast_nonneg N))
      ((div_le_one hN').mpr (Nat.cast_le.mpr hi))
      (by
        have h1 : ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = 1 / N := by
          push_cast
          field_simp
          ring
        rw [h1, abs_of_nonneg (by positivity), div_mul_eq_mul_div, one_mul,
          div_le_iff₀ hN']
        linarith) n
    exact ⟨e.trans e'⟩

include hg hβ hM h𝒲 hδ hT hτ hpb hpa htrap in
/-- The lens pairs in 𝒲 of g + 0 β and g + 1 β have isomorphic cohomology. -/
theorem nonempty_path_equiv (hM0 : 0 ≤ M) (n : ℕ) :
    Nonempty (H (triv (pairOf (partY_sub_partU (along g β 0)
        (retarget D (along_mono D h₁ le_rfl zero_le_one)) 𝒲 a b T))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU (along g β 1)
        (retarget D (along_mono D h₁ zero_le_one le_rfl)) 𝒲 a b T))) n) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M / δ)
  have hN0 : 0 < N := Nat.cast_pos.mp (lt_of_le_of_lt (div_nonneg hM0 hδ.le) hN)
  have hMN : M ≤ N * δ := ((div_lt_iff₀ hδ).mp hN).le
  obtain ⟨e⟩ := nonempty_steps D h₁ hg hβ hM h𝒲 hδ hT hτ hpb hpa htrap hN0 hMN n N le_rfl
  obtain ⟨e'⟩ := nonempty_step D h₁ hg hβ hM h𝒲 hδ hT hτ hpb hpa htrap
    (s := ((N : ℕ) : ℝ) / N) (s' := 1)
    (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg N))
    ((div_le_one (Nat.cast_pos.mpr hN0)).mpr le_rfl) zero_le_one le_rfl
    (by
      rw [div_self (ne_of_gt (Nat.cast_pos.mpr hN0)), sub_self, abs_zero, zero_mul]
      exact hδ.le) n
  exact ⟨e.trans e'⟩

end Main

end

end Finsler.LensPath
