module

public import Finsler.Definitions.Sphere
public import Mathlib.Algebra.Ring.Periodic

/-! Smooth one-periodic loops on the standard sphere, with image equality and
primitive period. These definitions do not assert the geodesic equation. -/

@[expose] public section

namespace Finsler.Loops

open Finsler.SphereGeometry Function
open scoped Manifold ContDiff

noncomputable section

structure SmoothLoop (n : ℕ) where
  curve : ℝ → Sphere n
  smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ curve
  periodic : Periodic curve 1

instance {n : ℕ} : CoeFun (SmoothLoop n) (fun _ => ℝ → Sphere n) := ⟨SmoothLoop.curve⟩

variable {n : ℕ}

@[ext] theorem loop_ext {γ δ : SmoothLoop n} (h : ∀ t, γ t = δ t) : γ = δ := by
  cases γ
  cases δ
  congr
  exact funext h

def image (γ : SmoothLoop n) : Set (Sphere n) := Set.range γ

def SameImage (γ δ : SmoothLoop n) : Prop := image γ = image δ

instance imageSetoid (n : ℕ) : Setoid (SmoothLoop n) where
  r := SameImage
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

abbrev ImageClass (n : ℕ) := Quotient (imageSetoid n)

def imageClass (γ : SmoothLoop n) : ImageClass n := Quotient.mk _ γ

theorem imageClass_eq_iff (γ δ : SmoothLoop n) :
    imageClass γ = imageClass δ ↔ image γ = image δ := Quotient.eq

def Nonconstant (γ : SmoothLoop n) : Prop := ∃ s t, γ s ≠ γ t

/-- The normalized period 1 is the least positive period. -/
def Primitive (γ : SmoothLoop n) : Prop :=
  ∀ T : ℝ, 0 < T → Periodic γ T → 1 ≤ T

def constant (x : Sphere n) : SmoothLoop n where
  curve := fun _ => x
  smooth := contMDiff_const
  periodic := fun _ => rfl

def shift (γ : SmoothLoop n) (a : ℝ) : SmoothLoop n where
  curve := fun t => γ (t + a)
  smooth := γ.smooth.comp (contDiff_id.add contDiff_const).contMDiff
  periodic := γ.periodic.add_const a

def reverse (γ : SmoothLoop n) : SmoothLoop n where
  curve := fun t => γ (-t)
  smooth := γ.smooth.comp contDiff_id.neg.contMDiff
  periodic := by
    intro t
    change γ (-(t + 1)) = γ (-t)
    convert γ.periodic.neg (-t) using 1
    congr 1
    ring

def iterate (γ : SmoothLoop n) (k : ℕ) : SmoothLoop n where
  curve := fun t => γ ((k : ℝ) * t)
  smooth := γ.smooth.comp (contDiff_const.mul contDiff_id).contMDiff
  periodic := by
    intro t
    change γ ((k : ℝ) * (t + 1)) = γ ((k : ℝ) * t)
    rw [mul_add, mul_one]
    simpa using γ.periodic.nat_mul k ((k : ℝ) * t)

theorem image_shift (γ : SmoothLoop n) (a : ℝ) : image (shift γ a) = image γ := by
  ext x
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t + a, h⟩
  · rintro ⟨t, h⟩
    refine ⟨t - a, ?_⟩
    simpa [shift] using h

theorem image_reverse (γ : SmoothLoop n) : image (reverse γ) = image γ := by
  ext x
  constructor
  · rintro ⟨t, h⟩
    exact ⟨-t, h⟩
  · rintro ⟨t, h⟩
    refine ⟨-t, ?_⟩
    simpa [reverse] using h

theorem image_iterate (γ : SmoothLoop n) {k : ℕ} (hk : k ≠ 0) :
    image (iterate γ k) = image γ := by
  ext x
  constructor
  · rintro ⟨t, h⟩
    exact ⟨(k : ℝ) * t, h⟩
  · rintro ⟨t, h⟩
    refine ⟨t / k, ?_⟩
    change γ ((k : ℝ) * (t / (k : ℝ))) = x
    rw [mul_div_cancel₀ t (show (k : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hk)]
    exact h

theorem reverse_reverse (γ : SmoothLoop n) : reverse (reverse γ) = γ := by
  ext t
  simp [reverse]

theorem shift_zero (γ : SmoothLoop n) : shift γ 0 = γ := by
  ext t
  simp [shift]

theorem shift_shift (γ : SmoothLoop n) (a b : ℝ) :
    shift (shift γ a) b = shift γ (b + a) := by
  ext t
  simp [shift, add_assoc]

theorem iterate_one (γ : SmoothLoop n) : iterate γ 1 = γ := by
  ext t
  simp [iterate]

theorem iterate_iterate (γ : SmoothLoop n) (k l : ℕ) :
    iterate (iterate γ k) l = iterate γ (k * l) := by
  ext t
  simp [iterate, Nat.cast_mul, mul_assoc]

theorem iterate_zero (γ : SmoothLoop n) : iterate γ 0 = constant (γ 0) := by
  ext t
  simp [iterate, constant]

theorem nonconstant_reverse_iff (γ : SmoothLoop n) :
    Nonconstant (reverse γ) ↔ Nonconstant γ := by
  constructor
  · rintro ⟨s, t, h⟩
    exact ⟨-s, -t, h⟩
  · rintro ⟨s, t, h⟩
    exact ⟨-s, -t, by simpa [reverse] using h⟩

theorem iterate_small_period (γ : SmoothLoop n) {k : ℕ} (hk : k ≠ 0) :
    Periodic (iterate γ k) (1 / k) := by
  intro t
  change γ ((k : ℝ) * (t + 1 / k)) = γ ((k : ℝ) * t)
  rw [mul_add, mul_one_div_cancel (Nat.cast_ne_zero.mpr hk)]
  exact γ.periodic _

theorem iterate_not_primitive (γ : SmoothLoop n) {k : ℕ} (hk : 1 < k) :
    ¬ Primitive (iterate γ k) := by
  intro h
  have hk0 : k ≠ 0 := by omega
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hle := h (1 / k) (one_div_pos.mpr (by positivity)) (iterate_small_period γ hk0)
  have hlt : (1 : ℝ) / k < 1 := (div_lt_one (by positivity)).mpr hkR
  exact (not_le_of_gt hlt) hle

/-- The explicit inverse to double iteration on its half-period fixed set. -/
def halfPeriodRoot (γ : SmoothLoop n) (hγ : Periodic γ (1 / 2)) : SmoothLoop n where
  curve := fun t => γ (t / 2)
  smooth := γ.smooth.comp (contDiff_id.div_const 2).contMDiff
  periodic := by
    intro t
    change γ ((t + 1) / 2) = γ (t / 2)
    rw [add_div]
    exact hγ _

theorem double_halfPeriodRoot (γ : SmoothLoop n) (hγ : Periodic γ (1 / 2)) :
    iterate (halfPeriodRoot γ hγ) 2 = γ := by
  apply loop_ext
  intro t
  change γ ((2 : ℝ) * t / 2) = γ t
  congr 1
  ring

theorem half_period_iff_double (γ : SmoothLoop n) :
    Periodic γ (1 / 2) ↔ ∃ δ : SmoothLoop n, iterate δ 2 = γ := by
  constructor
  · intro h
    exact ⟨halfPeriodRoot γ h, double_halfPeriodRoot γ h⟩
  · rintro ⟨δ, rfl⟩
    exact iterate_small_period δ (by decide)

theorem periodic_reverse_iff (γ : SmoothLoop n) (T : ℝ) :
    Periodic (reverse γ) T ↔ Periodic γ T := by
  constructor
  · intro h t
    have hh := h.neg (-t)
    change γ (-(-t + -T)) = γ (-(-t)) at hh
    simpa only [neg_add, neg_neg] using hh
  · intro h t
    change γ (-(t + T)) = γ (-t)
    simpa only [neg_add] using h.neg (-t)

theorem primitive_reverse_iff (γ : SmoothLoop n) : Primitive (reverse γ) ↔ Primitive γ := by
  unfold Primitive
  simp only [periodic_reverse_iff]

end

end Finsler.Loops
