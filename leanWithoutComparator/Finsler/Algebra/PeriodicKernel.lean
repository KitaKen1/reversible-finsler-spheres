module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Nat.GCD.Basic

/-! Vectors fixed by powers of an endomorphism. For an endomorphism M of a vector space, let
K_m be the space of the vectors fixed by M^m. Then K_a ≤ K_b when a divides b, and
K_a ⊓ K_b = K_{gcd(a,b)}. If the space is finite dimensional there is L ≥ 1 with
K_m = K_{gcd(m,L)} for all m ≥ 1: the dimensions of the K_m take only finitely many values, and
they depend on m only through gcd(m, L). This is the linear algebra behind the finitely many
types of the nullities of the iterates of a closed geodesic. -/

@[expose] public section

namespace Finsler.PeriodicKernel

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (M : V →ₗ[K] V)

/-- The vectors fixed by the m-th power of M. -/
def fixedPow (m : ℕ) : Submodule K V := LinearMap.ker (M ^ m - 1)

theorem mem_fixedPow {m : ℕ} {w : V} : w ∈ fixedPow M m ↔ (M ^ m) w = w := by
  rw [fixedPow, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- A vector fixed by M^a is fixed by M^(a c). -/
theorem pow_mul_apply {a : ℕ} {w : V} (hw : (M ^ a) w = w) (c : ℕ) : (M ^ (a * c)) w = w := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hw, ih]

theorem fixedPow_mono {a b : ℕ} (h : a ∣ b) : fixedPow M a ≤ fixedPow M b := by
  obtain ⟨c, rfl⟩ := h
  intro w hw
  rw [mem_fixedPow] at hw ⊢
  exact pow_mul_apply M hw c

/-- A vector fixed by M^a and by M^b is fixed by M^gcd(a, b). -/
theorem gcd_apply {w : V} (a b : ℕ) (ha : (M ^ a) w = w) (hb : (M ^ b) w = w) :
    (M ^ Nat.gcd a b) w = w := by
  induction a, b using Nat.gcd.induction with
  | H0 b => rwa [Nat.gcd_zero_left]
  | H1 a b hpos ih =>
    rw [Nat.gcd_rec]
    refine ih ?_ ha
    have h1 : (M ^ (b % a + a * (b / a))) w = w := by
      rw [Nat.mod_add_div]
      exact hb
    rw [pow_add, Module.End.mul_apply, pow_mul_apply M ha (b / a)] at h1
    exact h1

theorem fixedPow_inf (a b : ℕ) : fixedPow M a ⊓ fixedPow M b = fixedPow M (Nat.gcd a b) := by
  apply le_antisymm
  · intro w hw
    rw [mem_fixedPow]
    exact gcd_apply M a b ((mem_fixedPow M).mp hw.1) ((mem_fixedPow M).mp hw.2)
  · exact le_inf (fixedPow_mono M (Nat.gcd_dvd_left a b)) (fixedPow_mono M (Nat.gcd_dvd_right a b))

/-- The vectors fixed by the k-th power of M^d are the vectors fixed by M^(d k). -/
theorem fixedPow_pow (d k : ℕ) : fixedPow (M ^ d) k = fixedPow M (d * k) := by
  rw [fixedPow, fixedPow, pow_mul]

variable [FiniteDimensional K V]

/-- In finite dimension the spaces of the vectors fixed by the powers of M depend on the
exponent m ≥ 1 only through gcd(m, L), for some L ≥ 1. -/
theorem exists_period : ∃ L : ℕ, 1 ≤ L ∧ ∀ m : ℕ, 1 ≤ m →
    fixedPow M m = fixedPow M (Nat.gcd m L) := by
  -- an exponent with the largest dimension
  have hbdd : BddAbove (Set.range fun m : ℕ => finrank K (fixedPow M (m + 1))) :=
    ⟨finrank K V, by
      rintro _ ⟨m, rfl⟩
      exact Submodule.finrank_le _⟩
  obtain ⟨L₀, hL₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hmax : ∀ m : ℕ, finrank K (fixedPow M (m + 1)) ≤ finrank K (fixedPow M (L₀ + 1)) := by
    intro m
    have h := le_csSup hbdd (Set.mem_range_self m)
    have hL₀' : finrank K (fixedPow M (L₀ + 1)) =
        sSup (Set.range fun m : ℕ => finrank K (fixedPow M (m + 1))) := hL₀
    rw [hL₀']
    exact h
  refine ⟨L₀ + 1, Nat.succ_le_succ (Nat.zero_le _), fun m hm => ?_⟩
  have hlcm_pos : 1 ≤ Nat.lcm m (L₀ + 1) := Nat.lcm_pos hm (Nat.succ_pos _)
  have h1 : fixedPow M (L₀ + 1) ≤ fixedPow M (Nat.lcm m (L₀ + 1)) :=
    fixedPow_mono M (Nat.dvd_lcm_right m (L₀ + 1))
  have h2 : finrank K (fixedPow M (Nat.lcm m (L₀ + 1))) ≤ finrank K (fixedPow M (L₀ + 1)) := by
    have h := hmax (Nat.lcm m (L₀ + 1) - 1)
    rwa [Nat.sub_add_cancel hlcm_pos] at h
  have h3 : fixedPow M (L₀ + 1) = fixedPow M (Nat.lcm m (L₀ + 1)) :=
    Submodule.eq_of_le_of_finrank_le h1 h2
  have h4 : fixedPow M m ≤ fixedPow M (L₀ + 1) := by
    rw [h3]
    exact fixedPow_mono M (Nat.dvd_lcm_left m (L₀ + 1))
  rw [← fixedPow_inf]
  exact (inf_eq_left.mpr h4).symm

/-- The dimensions of the spaces of the vectors fixed by the powers of M depend on the exponent
only through gcd(m, L). -/
theorem exists_period_finrank : ∃ L : ℕ, 1 ≤ L ∧ ∀ m : ℕ, 1 ≤ m →
    finrank K (fixedPow M m) = finrank K (fixedPow M (Nat.gcd m L)) := by
  obtain ⟨L, hL, h⟩ := exists_period M
  exact ⟨L, hL, fun m hm => by rw [← h m hm]⟩

end Finsler.PeriodicKernel
