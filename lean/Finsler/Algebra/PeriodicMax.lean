module

public import Finsler.Algebra.PeriodicKernel

/-! A period from the dimensions alone. For an endomorphism M of a finite-dimensional vector
space, every exponent L ≥ 1 at which the space of the vectors fixed by M^L has maximal dimension
is a period: the vectors fixed by M^m are the vectors fixed by M^gcd(m, L) for all m ≥ 1. Hence
a period is determined by the function m ↦ dim ker(M^m - 1) alone. -/

@[expose] public section

namespace Finsler.PeriodicMax

open Module Finsler.PeriodicKernel

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (M : V →ₗ[K] V)

/-- **Every exponent of maximal dimension is a period.** -/
theorem eq_gcd_of_max {L : ℕ} (hL : 1 ≤ L)
    (hmax : ∀ m : ℕ, 1 ≤ m → finrank K (fixedPow M m) ≤ finrank K (fixedPow M L)) {m : ℕ}
    (hm : 1 ≤ m) : fixedPow M m = fixedPow M (Nat.gcd m L) := by
  have hlcm_pos : 1 ≤ Nat.lcm m L := Nat.lcm_pos hm hL
  have h1 : fixedPow M L ≤ fixedPow M (Nat.lcm m L) := fixedPow_mono M (Nat.dvd_lcm_right m L)
  have h3 : fixedPow M L = fixedPow M (Nat.lcm m L) :=
    Submodule.eq_of_le_of_finrank_le h1 (hmax _ hlcm_pos)
  have h4 : fixedPow M m ≤ fixedPow M L := by
    rw [h3]
    exact fixedPow_mono M (Nat.dvd_lcm_left m L)
  rw [← fixedPow_inf]
  exact (inf_eq_left.mpr h4).symm

/-- The dimensions at exponents with the same gcd with a maximal exponent agree. -/
theorem finrank_eq_of_max {L : ℕ} (hL : 1 ≤ L)
    (hmax : ∀ m : ℕ, 1 ≤ m → finrank K (fixedPow M m) ≤ finrank K (fixedPow M L)) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hg : Nat.gcd a L = Nat.gcd b L) :
    finrank K (fixedPow M a) = finrank K (fixedPow M b) := by
  rw [eq_gcd_of_max M hL hmax ha, eq_gcd_of_max M hL hmax hb, hg]

end Finsler.PeriodicMax
