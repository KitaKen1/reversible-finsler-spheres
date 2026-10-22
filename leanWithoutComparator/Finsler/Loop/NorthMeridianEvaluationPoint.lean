module

public import Finsler.Loop.OppositeMeridianEvaluationPoint

/-! Choose an ACTUAL rational north point Q=(3/5)P-(4/5)v0.
Its distance from the fixed meridian is at least4/5 and from the
closed southern hemisphere at least3/5. Thus evaluation radius<=1/2
excludes fixed returns, all southern legs, poles and equator seams. -/
@[expose] public section
namespace Finsler.NorthMeridianEvaluationPoint
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.RationalSphereArc Finsler.RationalSphereArcCoordinates
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def opposite {n : ℕ} {P : Sphere n} (v₀ : equator P) : equator P :=
  ⟨antipode v₀.val, by
    change ⟪(P : Ambient n), -(v₀.val : Ambient n)⟫ = 0
    rw [inner_neg_right, v₀.property, neg_zero]⟩

def target {n : ℕ} (P : Sphere n) (v₀ : equator P) : Sphere n :=
  point (outgoing P (opposite v₀)) ⟨1 / 2, by constructor <;> norm_num⟩

theorem target_value {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    (target P v₀ : Ambient n) = (3 / 5 : ℝ) • (P : Ambient n) - (4 / 5 : ℝ) • (v₀.val : Ambient n) := by
  rw [target, coordinates]
  change alpha ⟨1 / 2, _⟩ • (P : Ambient n) + beta ⟨1 / 2, _⟩ • (-(v₀.val : Ambient n)) = _
  norm_num [alpha, beta]
  module

theorem inner_pole_target {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    ⟪(P : Ambient n), (target P v₀ : Ambient n)⟫ = 3 / 5 := by
  rw [target_value, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    v₀.property, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp P.property]
  norm_num

theorem inner_fixed_target {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    ⟪(v₀.val : Ambient n), (target P v₀ : Ambient n)⟫ = -(4 / 5) := by
  have hv : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
  rw [target_value, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    hv,
    real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp v₀.val.property]
  norm_num

theorem distance_fixed_side {n : ℕ} (P : Sphere n) (v₀ : equator P) (y : Sphere n)
    (hy : 0 ≤ ⟪(v₀.val : Ambient n), (y : Ambient n)⟫) :
    (4 / 5 : ℝ) ≤ ‖(y : Ambient n) - (target P v₀ : Ambient n)‖ := by
  have h := real_inner_le_norm (v₀.val : Ambient n) ((y : Ambient n) - (target P v₀ : Ambient n))
  rw [inner_sub_right, inner_fixed_target, mem_sphere_zero_iff_norm.mp v₀.val.property, one_mul] at h
  linarith

theorem distance_south {n : ℕ} (P : Sphere n) (v₀ : equator P) (y : Sphere n)
    (hy : ⟪(P : Ambient n), (y : Ambient n)⟫ ≤ 0) :
    (3 / 5 : ℝ) ≤ ‖(y : Ambient n) - (target P v₀ : Ambient n)‖ := by
  have h := real_inner_le_norm (P : Ambient n) ((target P v₀ : Ambient n) - (y : Ambient n))
  rw [inner_sub_right, inner_pole_target, mem_sphere_zero_iff_norm.mp P.property, one_mul, norm_sub_rev] at h
  linarith

def excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (BorelEvaluation.sphere n) :=
  {y | 0 ≤ ⟪(v₀.val : Ambient n), (y : Ambient n)⟫ ∨ ⟪(P : Ambient n), (y : Ambient n)⟫ ≤ 0}

theorem excluded_distance {n : ℕ} (P : Sphere n) (v₀ : equator P) (y : excluded P v₀) :
    (3 / 5 : ℝ) ≤ ‖(y.val : Ambient n) - (target P v₀ : Ambient n)‖ := by
  rcases y.property with h | h
  · exact (by norm_num : (3 / 5 : ℝ) ≤ 4 / 5).trans (distance_fixed_side P v₀ y.val h)
  · exact distance_south P v₀ y.val h

theorem fixed_meridian_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : _root_.unitInterval) :
    meridian P v₀ t ∈ excluded P v₀ :=
  Or.inl (OppositeMeridianEvaluationPoint.meridian_inner_nonneg P v₀ t)

theorem incoming_excluded {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : _root_.unitInterval) :
    point (incoming P v) t ∈ excluded P v₀ := by
  apply Or.inr
  rw [coordinates, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  change alpha t * ⟪(P : Ambient n), (v.val : Ambient n)⟫ +
    beta t * ⟪(P : Ambient n), -(P : Ambient n)⟫ ≤ 0
  rw [v.property, inner_neg_right, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp P.property]
  nlinarith [beta_nonneg t]

theorem cocycle_pullback_zero {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) {X : TopCat.{0}}
    (f : X ⟶ BorelEvaluation.sphere n) (hf : ∀ x, f x ∈ excluded P v₀) :
    cochainPullback f n (LocalizedSphereTopCocycle.cocycle n hn (target P v₀) hη) = 0 := by
  apply LocalizedSphereTopCocycle.pullback_far_zero hn (target P v₀) hη f
  intro x
  exact hη2.trans ((by norm_num : (1 / 2 : ℝ) ≤ 3 / 5).trans (excluded_distance P v₀ ⟨f x, hf x⟩))

end
end Finsler.NorthMeridianEvaluationPoint
