module

public import Finsler.Loop.RationalSphereArcCoordinates
public import Finsler.Loop.MeridianIntersectionMaps

/-! A genuine continuous equator-direction map recovers the varying
parameter of every interior meridian point. Thus an interior
self-coincidence forces actual parameter equality. -/
@[expose] public section
namespace Finsler.MeridianInteriorDirection
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.RationalSphereArc
open Finsler.RationalSphereArcCoordinates Finsler.MeridianQuarterHomotopies
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def direction {n : ℕ} (P : Sphere n) : C(↥(upper P ∩ lower P), equator P) :=
  (MeridianIntersectionMaps.homotopyEquiv P).invFun

theorem direction_value {n : ℕ} (P : Sphere n) (x : ↥(upper P ∩ lower P)) :
    ((direction P x).val : Ambient n) =
      NormedSpace.normalize ((ℝ ∙ (P : Ambient n))ᗮ.starProjection (x.val : Ambient n)) := by
  exact TauCeti.coe_equatorHomotopyEquiv_apply P ((MeridianIntersectionMaps.reorder P).symm x)

theorem direction_positive_coordinates {n : ℕ} (P : Sphere n) (v : equator P)
    (x : ↥(upper P ∩ lower P)) {a b : ℝ} (hb : 0 < b)
    (hx : (x.val : Ambient n) = a • (P : Ambient n) + b • (v.val : Ambient n)) :
    direction P x = v := by
  apply Subtype.ext
  apply Subtype.ext
  rw [direction_value, hx, map_add, map_smul, map_smul,
    Submodule.starProjection_orthogonalComplement_singleton_eq_zero, smul_zero, zero_add]
  have hv : (v.val : Ambient n) ∈ (ℝ ∙ (P : Ambient n))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr v.property
  rw [Submodule.starProjection_eq_self_iff.mpr hv, NormedSpace.normalize_smul_of_pos hb,
    NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp v.val.property)]

theorem meridian_positive_coordinates {n : ℕ} (P : Sphere n) (v : equator P)
    (t : _root_.unitInterval) (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1) :
    ∃ a b : ℝ, 0 < b ∧ (meridian P v t : Ambient n) =
      a • (P : Ambient n) + b • (v.val : Ambient n) := by
  rw [meridian, Path.trans_apply]
  split_ifs with h
  · let s : _root_.unitInterval := ⟨2 * (t : ℝ), by constructor <;> linarith [t.property.1]⟩
    refine ⟨alpha s, beta s, beta_pos s (by dsimp [s]; linarith), ?_⟩
    change (point (outgoing P v) s : Ambient n) = _
    exact coordinates (outgoing P v) s
  · let s : _root_.unitInterval := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.2]⟩
    refine ⟨-beta s, alpha s, alpha_pos s (by dsimp [s]; linarith), ?_⟩
    change (point (incoming P v) s : Ambient n) = _
    rw [coordinates]
    change alpha s • (v.val : Ambient n) + beta s • (-(P : Ambient n)) = _
    module

theorem meridian_ne_poles {n : ℕ} (P : Sphere n) (v : equator P)
    (t : _root_.unitInterval) (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1) :
    meridian P v t ≠ P ∧ meridian P v t ≠ antipode P := by
  obtain ⟨a, b, hb, hx⟩ := meridian_positive_coordinates P v t ht₀ ht₁
  have hv : ⟪(v.val : Ambient n), (P : Ambient n)⟫ = 0 :=
    (real_inner_comm _ _).trans v.property
  have he : ⟪(v.val : Ambient n), (meridian P v t : Ambient n)⟫ = b := by
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right, hv,
      real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp v.val.property]
    simp
  constructor
  · intro h
    rw [h, hv] at he
    linarith
  · intro h
    rw [h] at he
    change ⟪(v.val : Ambient n), -(P : Ambient n)⟫ = b at he
    rw [inner_neg_right, hv, neg_zero] at he
    linarith

def interiorPoint {n : ℕ} (P : Sphere n) (v : equator P)
    (t : _root_.unitInterval) (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1) : ↥(upper P ∩ lower P) :=
  ⟨meridian P v t, (meridian_ne_poles P v t ht₀ ht₁).symm⟩

theorem direction_meridian {n : ℕ} (P : Sphere n) (v : equator P)
    (t : _root_.unitInterval) (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1) :
    direction P (interiorPoint P v t ht₀ ht₁) = v := by
  obtain ⟨a, b, hb, hx⟩ := meridian_positive_coordinates P v t ht₀ ht₁
  exact direction_positive_coordinates P v _ hb hx

theorem coincidence_direction {n : ℕ} (P : Sphere n) (v w : equator P)
    (s t : _root_.unitInterval) (hs₀ : 0 < (s : ℝ)) (hs₁ : (s : ℝ) < 1)
    (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1)
    (h : meridian P v s = meridian P w t) : v = w := by
  have he : interiorPoint P v s hs₀ hs₁ = interiorPoint P w t ht₀ ht₁ := Subtype.ext h
  have hd := congrArg (direction P) he
  rw [direction_meridian, direction_meridian] at hd
  exact hd

end
end Finsler.MeridianInteriorDirection
