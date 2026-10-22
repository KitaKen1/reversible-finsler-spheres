module

public import Finsler.Geometry.NearbyRotor
public import Mathlib.Topology.Homotopy.Basic

/-! A concrete deformation of the sphere's deleted diagonal to its antidiagonal.
This finite-dimensional construction is independent of a Finsler metric. -/

@[expose] public section

namespace Finsler.DiagonalGeometry

open Finsler.SphereGeometry Set
open scoped Topology RealInnerProductSpace

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

theorem sphere_norm (x : Sphere n) : ‖(x : Ambient n)‖ = 1 := by simpa using x.property

def antipodalHomeomorph (n : ℕ) : Sphere n ≃ₜ Sphere n where
  toFun x := ⟨-(x : Ambient n), by simpa using x.property⟩
  invFun x := ⟨-(x : Ambient n), by simpa using x.property⟩
  left_inv x := Subtype.ext (neg_neg _)
  right_inv x := Subtype.ext (neg_neg _)
  continuous_toFun := continuous_subtype_val.neg.subtype_mk _
  continuous_invFun := continuous_subtype_val.neg.subtype_mk _

def antipodal (n : ℕ) : C(Sphere n, Sphere n) :=
  ⟨antipodalHomeomorph n, (antipodalHomeomorph n).continuous⟩

theorem sphere_ne_antipodal (x : Sphere n) : x ≠ antipodalHomeomorph n x := by
  intro h
  have he := congrArg (fun y : Sphere n => ⟪(x : Ambient n), (y : Ambient n)⟫) h
  change ⟪(x : Ambient n), (x : Ambient n)⟫ = ⟪(x : Ambient n), -(x : Ambient n)⟫ at he
  rw [inner_neg_right, real_inner_self_eq_norm_sq, sphere_norm] at he
  norm_num at he

def deleted (n : ℕ) : Set (Sphere n × Sphere n) := {p | p.1 ≠ p.2}

theorem unit_ray_eq {x y : Ambient n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : a • y = b • x) : y = x := by
  have he := congrArg norm h
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha,
    Real.norm_of_nonneg hb.le, hx, hy, mul_one, mul_one] at he
  have hapos : 0 < a := he.symm ▸ hb
  rw [← he] at h
  have hc := congrArg (fun v : Ambient n => a⁻¹ • v) h
  simpa only [smul_smul, inv_mul_cancel₀ hapos.ne', one_smul] using hc

def chord (s : _root_.unitInterval) (p : deleted n) : Ambient n :=
  (1 - (s : ℝ)) • (p.val.2 : Ambient n) - (s : ℝ) • (p.val.1 : Ambient n)

theorem chord_ne_zero (s : _root_.unitInterval) (p : deleted n) : chord s p ≠ 0 := by
  intro h
  have he : (1 - (s : ℝ)) • (p.val.2 : Ambient n) = (s : ℝ) • (p.val.1 : Ambient n) :=
    sub_eq_zero.mp h
  have hn := congrArg norm he
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr s.property.2),
    Real.norm_of_nonneg s.property.1, sphere_norm, sphere_norm, mul_one, mul_one] at hn
  have hs : 0 < (s : ℝ) := by linarith
  exact p.property (Subtype.ext (unit_ray_eq (sphere_norm _) (sphere_norm _)
    (sub_nonneg.mpr s.property.2) hs he).symm)

def normalize (z : Ambient n) (hz : z ≠ 0) : Sphere n :=
  ⟨‖z‖⁻¹ • z, by
    have hn : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
    simpa using hn⟩

theorem normalized_chord_ne_first (s : _root_.unitInterval) (p : deleted n) :
    normalize (chord s p) (chord_ne_zero s p) ≠ p.val.1 := by
  intro h
  have hz : 0 < ‖chord s p‖ := norm_pos_iff.mpr (chord_ne_zero s p)
  have he := congrArg (fun x : Sphere n => ‖chord s p‖ • (x : Ambient n)) h
  have hc : chord s p = ‖chord s p‖ • (p.val.1 : Ambient n) := by
    simpa only [normalize, smul_smul, mul_inv_cancel₀ hz.ne', one_smul] using he
  have hr : (1 - (s : ℝ)) • (p.val.2 : Ambient n) =
      ((s : ℝ) + ‖chord s p‖) • (p.val.1 : Ambient n) := by
    have hh := eq_add_of_sub_eq hc
    simpa only [chord, add_smul, add_comm] using hh
  have hp : 0 < (s : ℝ) + ‖chord s p‖ := by linarith [s.property.1]
  exact p.property (Subtype.ext (unit_ray_eq (sphere_norm _) (sphere_norm _)
    (sub_nonneg.mpr s.property.2) hp hr).symm)

def deform (s : _root_.unitInterval) (p : deleted n) : deleted n :=
  ⟨(p.val.1, normalize (chord s p) (chord_ne_zero s p)),
    (normalized_chord_ne_first s p).symm⟩

theorem continuous_deform : Continuous (fun p : _root_.unitInterval × deleted n =>
    deform p.1 p.2) := by
  have hs : Continuous (fun p : _root_.unitInterval × deleted n => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : _root_.unitInterval × deleted n =>
      (p.2.val.1 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
  have hy : Continuous (fun p : _root_.unitInterval × deleted n =>
      (p.2.val.2 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
  have hc : Continuous (fun p : _root_.unitInterval × deleted n => chord p.1 p.2) :=
    ((continuous_const.sub hs).smul hy).sub (hs.smul hx)
  have hi : Continuous (fun p : _root_.unitInterval × deleted n => ‖chord p.1 p.2‖⁻¹) :=
    hc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (chord_ne_zero p.1 p.2))
  have hn : Continuous (fun p : _root_.unitInterval × deleted n =>
      normalize (chord p.1 p.2) (chord_ne_zero p.1 p.2)) := (hi.smul hc).subtype_mk _
  have hp : Continuous (fun p : _root_.unitInterval × deleted n => p.2.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  exact (hp.prodMk hn).subtype_mk _

def first (n : ℕ) : C(deleted n, Sphere n) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

def second (n : ℕ) : C(deleted n, Sphere n) :=
  ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩

def sectionMap (n : ℕ) : C(Sphere n, deleted n) :=
  ⟨fun x => ⟨(x, antipodalHomeomorph n x), sphere_ne_antipodal x⟩,
    (continuous_id.prodMk (antipodalHomeomorph n).continuous).subtype_mk _⟩

theorem deform_zero (p : deleted n) : deform 0 p = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ‖chord 0 p‖⁻¹ • chord 0 p = (p.val.2 : Ambient n)
    simp only [chord, show ((0 : _root_.unitInterval) : ℝ) = 0 from rfl,
      sub_zero, one_smul, zero_smul, sphere_norm, inv_one]

theorem deform_one (p : deleted n) : deform 1 p = sectionMap n (first n p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ‖chord 1 p‖⁻¹ • chord 1 p = -(p.val.1 : Ambient n)
    simp only [chord, show ((1 : _root_.unitInterval) : ℝ) = 1 from rfl,
      sub_self, zero_smul, one_smul, zero_sub, norm_neg, sphere_norm, inv_one]

def retractionHomotopy (n : ℕ) :
    (ContinuousMap.id (deleted n)).Homotopy ((sectionMap n).comp (first n)) where
  toFun p := deform p.1 p.2
  continuous_toFun := continuous_deform
  map_zero_left := deform_zero
  map_one_left := deform_one

def projectionHomotopy (n : ℕ) :
    (second n).Homotopy ((antipodal n).comp (first n)) where
  toFun p := second n (deform p.1 p.2)
  continuous_toFun := (second n).continuous.comp continuous_deform
  map_zero_left p := congrArg (second n) (deform_zero p)
  map_one_left p := congrArg (second n) (deform_one p)


end
end Finsler.DiagonalGeometry
