module

public import Finsler.Geometry.CircleHalfRotation

/-! The reduced half action is the identity for even normal multiplicity, and the
root half rotation for odd multiplicity. These are equalities of actual vertex shifts. -/

@[expose] public section

namespace Finsler.RootHalfParity

open Finsler.PolygonIterate Finsler.CircleHalfRotation

theorem reduced_even (m s N : ℕ) (hm : Even m) :
    red m (s * (2 * N)) (halfIndex m s N) = 0 := by
  obtain ⟨r, hr⟩ := hm
  have he : m * s * N = r * (s * (2 * N)) := by rw [hr]; ring
  change red m (s * (2 * N)) ((m * s * N : ℕ) : ZMod (m * (s * (2 * N)))) = 0
  rw [red_natCast, he, Nat.cast_mul, ZMod.natCast_self, mul_zero]

theorem reduced_odd (m s N : ℕ) (hm : Odd m) :
    red m (s * (2 * N)) (halfIndex m s N) = (s * N : ℕ) := by
  obtain ⟨r, hr⟩ := hm
  have he : m * s * N = r * (s * (2 * N)) + s * N := by rw [hr]; ring
  change red m (s * (2 * N)) ((m * s * N : ℕ) : ZMod (m * (s * (2 * N)))) = (s * N : ℕ)
  rw [red_natCast, he, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

end Finsler.RootHalfParity
