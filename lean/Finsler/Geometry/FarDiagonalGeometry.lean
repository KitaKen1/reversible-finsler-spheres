module

public import Finsler.Topology.DiagonalAvoidanceCocycle

/-! The existing deleted-diagonal chord deformation preserves every positive
far-distance threshold. Thus the actual far set retracts to the antidiagonal,
with no replacement by a homotopy-equivalent unspecified space. -/

@[expose] public section
namespace Finsler.FarDiagonalGeometry

open Finsler.SphereGeometry Finsler.DiagonalGeometry
open Finsler.DiagonalAvoidanceCocycle Set
open scoped Topology RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {n : ℕ}

theorem chord_norm_le_one (s : _root_.unitInterval) (p : deleted n) : ‖chord s p‖ ≤ 1 := by
  have h := norm_sub_le ((1 - (s : ℝ)) • (p.val.2 : Ambient n))
    ((s : ℝ) • (p.val.1 : Ambient n))
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr s.property.2),
    Real.norm_of_nonneg s.property.1, sphere_norm, sphere_norm, mul_one, mul_one] at h
  exact h.trans_eq (by ring)

theorem chord_norm_lower (s : _root_.unitInterval) (p : deleted n) :
    1 - 2 * (s : ℝ) ≤ ‖chord s p‖ := by
  have h := norm_add_le (chord s p) ((s : ℝ) • (p.val.1 : Ambient n))
  have he : chord s p + (s : ℝ) • (p.val.1 : Ambient n) =
      (1 - (s : ℝ)) • (p.val.2 : Ambient n) := by simp [chord]
  rw [he, norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr s.property.2),
    Real.norm_of_nonneg s.property.1, sphere_norm, sphere_norm, mul_one, mul_one] at h
  linarith

theorem inner_normalized_chord (s : _root_.unitInterval) (p : deleted n) :
    ⟪(normalize (chord s p) (chord_ne_zero s p) : Ambient n), (p.val.1 : Ambient n)⟫ =
      ((1 - (s : ℝ)) * ⟪(p.val.2 : Ambient n), (p.val.1 : Ambient n)⟫ - (s : ℝ)) /
        ‖chord s p‖ := by
  change ⟪‖chord s p‖⁻¹ • chord s p, (p.val.1 : Ambient n)⟫ = _
  rw [real_inner_smul_left, chord, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, sphere_norm]
  simp only [one_pow, mul_one]
  ring

theorem normalized_inner_le (s : _root_.unitInterval) (p : deleted n) :
    ⟪(normalize (chord s p) (chord_ne_zero s p) : Ambient n), (p.val.1 : Ambient n)⟫ ≤
      ⟪(p.val.2 : Ambient n), (p.val.1 : Ambient n)⟫ := by
  have hN : 0 < ‖chord s p‖ := norm_pos_iff.mpr (chord_ne_zero s p)
  have hi := abs_real_inner_le_norm (p.val.2 : Ambient n) (p.val.1 : Ambient n)
  rw [sphere_norm, sphere_norm, mul_one] at hi
  have hc := abs_le.mp hi
  rw [inner_normalized_chord, div_le_iff₀ hN]
  by_cases h : 0 ≤ ⟪(p.val.2 : Ambient n), (p.val.1 : Ambient n)⟫
  · have hb := mul_le_mul_of_nonneg_left (chord_norm_lower s p) h
    nlinarith [s.property.1, mul_nonneg s.property.1 (sub_nonneg.mpr hc.2)]
  · have hb := mul_le_mul_of_nonpos_left (chord_norm_le_one s p) (le_of_not_ge h)
    nlinarith [mul_nonneg s.property.1 (show 0 ≤
      ⟪(p.val.2 : Ambient n), (p.val.1 : Ambient n)⟫ + 1 by linarith)]

theorem distance_nondecreasing (s : _root_.unitInterval) (p : deleted n) :
    ‖(p.val.2 : Ambient n) - p.val.1‖ ≤
      ‖((deform s p).val.2 : Ambient n) - (deform s p).val.1‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_sub_sq_real, sphere_norm, sphere_norm, sphere_norm, sphere_norm]
  have hi : ⟪((deform s p).val.2 : Ambient n), ((deform s p).val.1 : Ambient n)⟫ ≤
      ⟪(p.val.2 : Ambient n), (p.val.1 : Ambient n)⟫ := normalized_inner_le s p
  nlinarith

def firstFar {ρ : ℝ} : C(far n ρ, Sphere n) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

theorem antipodal_distance (x : Sphere n) :
    ‖(antipodalHomeomorph n x : Ambient n) - x‖ = 2 := by
  have he : (antipodalHomeomorph n x : Ambient n) - x = (-2 : ℝ) • (x : Ambient n) := by
    change -(x : Ambient n) - x = _
    module
  rw [he, norm_smul, sphere_norm]
  norm_num

def sectionFar {ρ : ℝ} (hρ : ρ ≤ 2) : C(Sphere n, far n ρ) := by
  have hm (x : Sphere n) : (x, antipodalHomeomorph n x) ∈ far n ρ := by
    change ρ ≤ ‖(antipodalHomeomorph n x : Ambient n) - x‖
    rw [antipodal_distance]
    exact hρ
  exact ⟨fun x => ⟨(x, antipodalHomeomorph n x), hm x⟩,
    (continuous_id.prodMk (antipodalHomeomorph n).continuous).subtype_mk hm⟩

def deformFar {ρ : ℝ} (hρ : 0 < ρ) (s : _root_.unitInterval) (p : far n ρ) : far n ρ :=
  ⟨(deform s (farToDeleted n hρ p)).val, p.property.trans
    (distance_nondecreasing s (farToDeleted n hρ p))⟩

theorem continuous_deformFar {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (fun z : _root_.unitInterval × far n ρ => deformFar hρ z.1 z.2) :=
  (continuous_subtype_val.comp (continuous_deform.comp
    (continuous_fst.prodMk ((farToDeleted n hρ).hom.continuous.comp continuous_snd)))).subtype_mk _

theorem deformFar_zero {ρ : ℝ} (hρ : 0 < ρ) (p : far n ρ) : deformFar hρ 0 p = p := by
  apply Subtype.ext
  exact congrArg (fun q : deleted n => q.val) (deform_zero (farToDeleted n hρ p))

theorem deformFar_one {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) (p : far n ρ) :
    deformFar hρ 1 p = sectionFar hρ2 (firstFar p) := by
  apply Subtype.ext
  exact congrArg (fun q : deleted n => q.val) (deform_one (farToDeleted n hρ p))

def retractionHomotopy {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    (ContinuousMap.id (far n ρ)).Homotopy ((sectionFar hρ2).comp firstFar) where
  toFun z := deformFar hρ z.1 z.2
  continuous_toFun := continuous_deformFar hρ
  map_zero_left p := deformFar_zero hρ p
  map_one_left p := deformFar_one hρ hρ2 p

end
end Finsler.FarDiagonalGeometry
