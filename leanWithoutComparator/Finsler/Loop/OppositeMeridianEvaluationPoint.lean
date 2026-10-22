module

public import Finsler.Loop.LocalizedSphereTopCocycle
public import Finsler.Loop.MeridianInteriorDirection

/-! An explicit evaluation localization point OPPOSITE the fixed
equator direction. The entire original fixed meridian, including
both poles and both return quarters, stays a uniform positive
distance away. The EXISTING sphere top cocycle therefore vanishes
literally on every family whose evaluation lies on that curve. -/
@[expose] public section
namespace Finsler.OppositeMeridianEvaluationPoint
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.RationalSphereArc Finsler.RationalSphereArcCoordinates
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

def target {n : ℕ} {P : Sphere n} (v₀ : equator P) : Sphere n := antipode v₀.val

theorem inner_target {n : ℕ} {P : Sphere n} (v₀ : equator P) :
    ⟪(v₀.val : Ambient n), (target v₀ : Ambient n)⟫ = -1 := by
  change ⟪(v₀.val : Ambient n), -(v₀.val : Ambient n)⟫ = -1
  rw [inner_neg_right, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp v₀.val.property]
  norm_num

theorem meridian_inner_nonneg {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : _root_.unitInterval) :
    0 ≤ ⟪(v₀.val : Ambient n), (meridian P v₀ t : Ambient n)⟫ := by
  have hv : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
  have hn : ‖(v₀.val : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp v₀.val.property
  rw [meridian, Path.trans_apply]
  split_ifs with h
  · let s : _root_.unitInterval := ⟨2 * (t : ℝ), by constructor <;> linarith [t.property.1]⟩
    change 0 ≤ ⟪(v₀.val : Ambient n), (point (outgoing P v₀) s : Ambient n)⟫
    rw [coordinates, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    change 0 ≤ alpha s * ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ +
      beta s * ⟪(v₀.val : Ambient n), (v₀.val : Ambient n)⟫
    rw [hv, real_inner_self_eq_norm_sq, hn]
    simpa using beta_nonneg s
  · let s : _root_.unitInterval := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.2]⟩
    change 0 ≤ ⟪(v₀.val : Ambient n), (point (incoming P v₀) s : Ambient n)⟫
    rw [coordinates, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    change 0 ≤ alpha s * ⟪(v₀.val : Ambient n), (v₀.val : Ambient n)⟫ +
      beta s * ⟪(v₀.val : Ambient n), -(P : Ambient n)⟫
    rw [inner_neg_right, hv, real_inner_self_eq_norm_sq, hn]
    simpa using alpha_nonneg s

theorem meridian_avoids_target {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : _root_.unitInterval) :
    meridian P v₀ t ≠ target v₀ := by
  intro he
  have hn := meridian_inner_nonneg P v₀ t
  rw [he, inner_target] at hn
  norm_num at hn

theorem poles_avoid_target {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    P ≠ target v₀ ∧ antipode P ≠ target v₀ := by
  have h0 := meridian_avoids_target P v₀ 0
  have h1 := meridian_avoids_target P v₀ 1
  simpa only [Path.source, Path.target] using And.intro h0 h1

theorem distance_sq_ge_two {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : _root_.unitInterval) :
    2 ≤ ‖(meridian P v₀ t : Ambient n) - (target v₀ : Ambient n)‖ ^ 2 := by
  change 2 ≤ ‖(meridian P v₀ t : Ambient n) - (-(v₀.val : Ambient n))‖ ^ 2
  rw [sub_neg_eq_add, norm_add_sq_real, mem_sphere_zero_iff_norm.mp (meridian P v₀ t).property,
    mem_sphere_zero_iff_norm.mp v₀.val.property, real_inner_comm]
  linarith [meridian_inner_nonneg P v₀ t]

theorem distance_gt_one {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : _root_.unitInterval) :
    1 < ‖(meridian P v₀ t : Ambient n) - (target v₀ : Ambient n)‖ := by
  have hs := distance_sq_ge_two P v₀ t
  have hn := norm_nonneg ((meridian P v₀ t : Ambient n) - (target v₀ : Ambient n))
  nlinarith

theorem exists_radius {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : _root_.unitInterval,
      R ≤ ‖(meridian P v₀ t : Ambient n) - (target v₀ : Ambient n)‖ := by
  exact ⟨1, zero_lt_one, fun t => (distance_gt_one P v₀ t).le⟩

def radius {n : ℕ} (_P : Sphere n) (_v₀ : equator _P) : ℝ := 1
theorem radius_positive {n : ℕ} (P : Sphere n) (v₀ : equator P) : 0 < radius P v₀ :=
  zero_lt_one
theorem radius_spec {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : _root_.unitInterval) :
    radius P v₀ ≤ ‖(meridian P v₀ t : Ambient n) - (target v₀ : Ambient n)‖ :=
  (distance_gt_one P v₀ t).le

theorem family_pullback_zero {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hηR : η ≤ radius P v₀) {X : TopCat.{0}}
    (f : X ⟶ BorelEvaluation.sphere n)
    (hf : ∀ x, ∃ t : _root_.unitInterval, f x = meridian P v₀ t) :
    cochainPullback f n (LocalizedSphereTopCocycle.cocycle n hn (target v₀) hη) = 0 := by
  apply LocalizedSphereTopCocycle.pullback_far_zero hn (target v₀) hη f
  intro x
  obtain ⟨t, ht⟩ := hf x
  rw [ht]
  exact hηR.trans (radius_spec P v₀ t)

end
end Finsler.OppositeMeridianEvaluationPoint
