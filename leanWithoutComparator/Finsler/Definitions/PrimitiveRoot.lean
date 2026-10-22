module

public import Finsler.Definitions.Loop
public import Mathlib.Topology.Algebra.Order.Archimedean

/-! A nonconstant continuous periodic loop has a least positive real period.
The primitive root is explicitly γ(T * t). No geodesic flow or ODE is used. -/

@[expose] public section

namespace Finsler.Loops

open Finsler.SphereGeometry Function
open scoped Manifold ContDiff

noncomputable section

variable {n : ℕ}

def periodSubgroup (γ : SmoothLoop n) : AddSubgroup ℝ where
  carrier := {T | Periodic γ T}
  zero_mem' := by intro t; simp
  add_mem' := fun h h' => h.add_period h'
  neg_mem' := fun h => h.neg

theorem mem_periodSubgroup (γ : SmoothLoop n) (T : ℝ) :
    T ∈ periodSubgroup γ ↔ Periodic γ T := Iff.rfl

theorem periodSubgroup_ne_bot (γ : SmoothLoop n) : periodSubgroup γ ≠ ⊥ := by
  intro h
  have h1 : (1 : ℝ) ∈ periodSubgroup γ := γ.periodic
  rw [h, AddSubgroup.mem_bot] at h1
  norm_num at h1

theorem periodSubgroup_not_dense (γ : SmoothLoop n) (hγ : Nonconstant γ) :
    ¬ Dense (periodSubgroup γ : Set ℝ) := by
  intro hd
  have he : (γ : ℝ → Sphere n) = fun _ => γ 0 :=
    Continuous.ext_on hd γ.smooth.continuous continuous_const (fun T hT => by
      simpa using hT 0)
  rcases hγ with ⟨s, t, hst⟩
  exact hst ((congrFun he s).trans (congrFun he t).symm)

theorem exists_least_positive_period (γ : SmoothLoop n) (hγ : Nonconstant γ) :
    ∃ T : ℝ, IsLeast {S | Periodic γ S ∧ 0 < S} T := by
  by_contra h
  exact periodSubgroup_not_dense γ hγ
    ((periodSubgroup γ).dense_of_no_min (periodSubgroup_ne_bot γ) h)

theorem least_period_integer_multiple (γ : SmoothLoop n) {T : ℝ}
    (hT : IsLeast {S | Periodic γ S ∧ 0 < S} T) :
    ∃ k : ℕ, 0 < k ∧ T * (k : ℝ) = 1 := by
  have he : periodSubgroup γ = AddSubgroup.zmultiples T := by
    rw [AddSubgroup.zmultiples_eq_closure]
    exact AddSubgroup.cyclic_of_min hT
  have h1 : (1 : ℝ) ∈ periodSubgroup γ := γ.periodic
  rw [he] at h1
  rcases AddSubgroup.mem_zmultiples_iff.mp h1 with ⟨k, hk⟩
  have hkR : (k : ℝ) * T = 1 := by simpa only [zsmul_eq_mul] using hk
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := (mul_pos_iff_of_pos_right hT.1.2).mp (by rw [hkR]; norm_num)
    exact_mod_cast this
  refine ⟨k.toNat, by omega, ?_⟩
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hkpos.le
  rw [hcast, mul_comm]
  exact hkR

def periodRoot (γ : SmoothLoop n) (T : ℝ) (hT : Periodic γ T) : SmoothLoop n where
  curve := fun t => γ (T * t)
  smooth := γ.smooth.comp (contDiff_const.mul contDiff_id).contMDiff
  periodic := by intro t; change γ (T * (t + 1)) = γ (T * t); simpa [mul_add] using hT (T * t)

theorem image_periodRoot (γ : SmoothLoop n) {T : ℝ} (hT : Periodic γ T) (hT0 : T ≠ 0) :
    image (periodRoot γ T hT) = image γ := by
  ext x
  constructor
  · rintro ⟨t, h⟩
    exact ⟨T * t, h⟩
  · rintro ⟨t, h⟩
    refine ⟨t / T, ?_⟩
    change γ (T * (t / T)) = x
    rw [mul_div_cancel₀ t hT0]
    exact h

theorem periodic_periodRoot_iff (γ : SmoothLoop n) {T : ℝ} (hT : Periodic γ T)
    (hT0 : T ≠ 0) (S : ℝ) :
    Periodic (periodRoot γ T hT) S ↔ Periodic γ (T * S) := by
  constructor
  · intro h t
    have hh := h (t / T)
    change γ (T * (t / T + S)) = γ (T * (t / T)) at hh
    simpa only [mul_add, mul_div_cancel₀ t hT0] using hh
  · intro h t
    change γ (T * (t + S)) = γ (T * t)
    simpa only [mul_add] using h (T * t)

theorem primitive_periodRoot (γ : SmoothLoop n) {T : ℝ}
    (hT : IsLeast {S | Periodic γ S ∧ 0 < S} T) :
    Primitive (periodRoot γ T hT.1.1) := by
  intro S hS hper
  have hTS := (periodic_periodRoot_iff γ hT.1.1 (ne_of_gt hT.1.2) S).mp hper
  have hle : T ≤ T * S := hT.2 ⟨hTS, mul_pos hT.1.2 hS⟩
  exact (le_mul_iff_one_le_right hT.1.2).mp hle

theorem iterate_periodRoot (γ : SmoothLoop n) {T : ℝ} (hT : Periodic γ T)
    (k : ℕ) (hk : T * (k : ℝ) = 1) : iterate (periodRoot γ T hT) k = γ := by
  apply loop_ext
  intro t
  change γ (T * ((k : ℝ) * t)) = γ t
  rw [← mul_assoc, hk, one_mul]

theorem exists_primitive_root (γ : SmoothLoop n) (hγ : Nonconstant γ) :
    ∃ δ : SmoothLoop n, ∃ k : ℕ, 0 < k ∧ Primitive δ ∧ iterate δ k = γ := by
  rcases exists_least_positive_period γ hγ with ⟨T, hT⟩
  rcases least_period_integer_multiple γ hT with ⟨k, hk, hTk⟩
  exact ⟨periodRoot γ T hT.1.1, k, hk, primitive_periodRoot γ hT,
    iterate_periodRoot γ hT.1.1 k hTk⟩

theorem primitive_iff_not_multiple (γ : SmoothLoop n) (hγ : Nonconstant γ) :
    Primitive γ ↔ ¬ ∃ δ : SmoothLoop n, ∃ k : ℕ, 1 < k ∧ iterate δ k = γ := by
  constructor
  · intro hp
    rintro ⟨δ, k, hk, rfl⟩
    exact iterate_not_primitive δ hk hp
  · intro h
    rcases exists_primitive_root γ hγ with ⟨δ, k, hk, hp, he⟩
    have hk1 : k = 1 := by
      by_contra hne
      exact h ⟨δ, k, by omega, he⟩
    rw [hk1, iterate_one] at he
    exact he ▸ hp

end

end Finsler.Loops
