module

public import Finsler.Topology.NormalizedDiagonalCocycle
public import Finsler.Loop.CloseSphereHomotopy

/-! Move the second point away from the first along a genuine
continuous orthogonal unit field. For every radius at most ONE the
closed far carrier is preserved throughout the real homotopy. The
endpoint pair is entirely far. This is the geometric excess-direction
shortcut; no dimension theorem or zero Thom pullback is assumed. -/
@[expose] public section
namespace Finsler.OrthogonalSphereEscape
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelEvaluation
open Finsler.DiagonalGeometry
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def blend {n : ℕ} (s : ClosedInterval) (y w : Sphere n) : Ambient n :=
  (1 - (s : ℝ)) • (y : Ambient n) + (s : ℝ) • (w : Ambient n)

theorem inner_blend_left {n : ℕ} (s : ClosedInterval) (y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) :
    ⟪(y : Ambient n), blend s y w⟫ = 1 - (s : ℝ) := by
  rw [blend, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    hyw, real_inner_self_eq_norm_sq, sphere_norm]
  ring

theorem inner_blend_right {n : ℕ} (s : ClosedInterval) (y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) :
    ⟪(w : Ambient n), blend s y w⟫ = (s : ℝ) := by
  rw [blend, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    ← real_inner_comm (w : Ambient n) (y : Ambient n), hyw, real_inner_self_eq_norm_sq, sphere_norm]
  ring

theorem blend_ne_zero {n : ℕ} (s : ClosedInterval) (y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) : blend s y w ≠ 0 := by
  intro hz
  have hl := inner_blend_left s y w hyw
  have hr := inner_blend_right s y w hyw
  rw [hz, inner_zero_right] at hl hr
  linarith

theorem blend_norm_lower {n : ℕ} (s : ClosedInterval) (y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) : 1 - (s : ℝ) ≤ ‖blend s y w‖ := by
  have h := real_inner_le_norm (y : Ambient n) (blend s y w)
  rw [inner_blend_left s y w hyw, sphere_norm, one_mul] at h
  exact h

def point {n : ℕ} (s : ClosedInterval) (y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) : Sphere n :=
  DiagonalGeometry.normalize (blend s y w) (blend_ne_zero s y w hyw)

theorem inner_point {n : ℕ} (s : ClosedInterval) (x y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0)
    (hxw : ⟪(x : Ambient n), (w : Ambient n)⟫ = 0) :
    ⟪(x : Ambient n), (point s y w hyw : Ambient n)⟫ =
      ((1 - (s : ℝ)) / ‖blend s y w‖) * ⟪(x : Ambient n), (y : Ambient n)⟫ := by
  change ⟪(x : Ambient n), ‖blend s y w‖⁻¹ • blend s y w⟫ = _
  rw [real_inner_smul_right, blend, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, hxw]
  ring

theorem coefficient_nonneg {n : ℕ} (s : ClosedInterval) (y w : Sphere n) :
    0 ≤ (1 - (s : ℝ)) / ‖blend s y w‖ := div_nonneg (sub_nonneg.mpr s.property.2) (norm_nonneg _)

theorem coefficient_le_one {n : ℕ} (s : ClosedInterval) (y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) :
    (1 - (s : ℝ)) / ‖blend s y w‖ ≤ 1 :=
  (div_le_one (norm_pos_iff.mpr (blend_ne_zero s y w hyw))).mpr (blend_norm_lower s y w hyw)

theorem inner_bound {n : ℕ} (s : ClosedInterval) (x y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0)
    (hxw : ⟪(x : Ambient n), (w : Ambient n)⟫ = 0) {c : ℝ} (hc : 0 ≤ c)
    (hxy : ⟪(x : Ambient n), (y : Ambient n)⟫ ≤ c) :
    ⟪(x : Ambient n), (point s y w hyw : Ambient n)⟫ ≤ c := by
  rw [inner_point s x y w hyw hxw]
  exact (mul_le_mul_of_nonneg_left hxy (coefficient_nonneg s y w)).trans
    (mul_le_of_le_one_left hc (coefficient_le_one s y w hyw))

theorem far_preserved {n : ℕ} (s : ClosedInterval) (x y w : Sphere n)
    (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0)
    (hxw : ⟪(x : Ambient n), (w : Ambient n)⟫ = 0)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hfar : ρ ≤ ‖(y : Ambient n) - x‖) :
    ρ ≤ ‖(point s y w hyw : Ambient n) - x‖ := by
  have hxy := norm_sub_sq_real (y : Ambient n) (x : Ambient n)
  rw [sphere_norm, sphere_norm, ← real_inner_comm (y : Ambient n) (x : Ambient n)] at hxy
  have hi : ⟪(x : Ambient n), (y : Ambient n)⟫ ≤ 1 - ρ ^ 2 / 2 := by
    nlinarith [sq_le_sq₀ hρ (norm_nonneg ((y : Ambient n) - x)) |>.mpr hfar]
  have hc : 0 ≤ 1 - ρ ^ 2 / 2 := by nlinarith
  have hb := inner_bound s x y w hyw hxw hc hi
  have hp := norm_sub_sq_real (point s y w hyw : Ambient n) (x : Ambient n)
  rw [sphere_norm, sphere_norm, ← real_inner_comm (point s y w hyw : Ambient n) (x : Ambient n)] at hp
  nlinarith [norm_nonneg ((point s y w hyw : Ambient n) - x)]

theorem point_zero {n : ℕ} (y w : Sphere n) (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) :
    point 0 y w hyw = y := by
  apply Subtype.ext
  change ‖blend 0 y w‖⁻¹ • blend 0 y w = (y : Ambient n)
  simp only [blend, show ((0 : ClosedInterval) : ℝ) = 0 from rfl, sub_zero,
    one_smul, zero_smul, add_zero, sphere_norm, inv_one]

theorem point_one {n : ℕ} (y w : Sphere n) (hyw : ⟪(y : Ambient n), (w : Ambient n)⟫ = 0) :
    point 1 y w hyw = w := by
  apply Subtype.ext
  change ‖blend 1 y w‖⁻¹ • blend 1 y w = (w : Ambient n)
  simp only [blend, show ((1 : ClosedInterval) : ℝ) = 1 from rfl, sub_self,
    zero_smul, one_smul, zero_add, sphere_norm, inv_one]

theorem orthogonal_far {n : ℕ} (x w : Sphere n) (hxw : ⟪(x : Ambient n), (w : Ambient n)⟫ = 0)
    {ρ : ℝ} (hρ : ρ ≤ 1) : ρ ≤ ‖(w : Ambient n) - x‖ := by
  have he := norm_sub_sq_real (w : Ambient n) (x : Ambient n)
  rw [sphere_norm, sphere_norm, ← real_inner_comm (w : Ambient n) (x : Ambient n), hxw] at he
  nlinarith [norm_nonneg ((w : Ambient n) - x)]

variable {n : ℕ} {X : TopCat.{0}} (f g w : X ⟶ sphere n)
  (hgw : ∀ x, ⟪(g x : Ambient n), (w x : Ambient n)⟫ = 0)
  (hfw : ∀ x, ⟪(f x : Ambient n), (w x : Ambient n)⟫ = 0)

def pair : X ⟶ DiagonalCohomology.product n :=
  TopCat.ofHom ⟨fun x => (f x, g x), f.hom.continuous.prodMk g.hom.continuous⟩

def escaped : X ⟶ DiagonalCohomology.product n := pair f w

def homotopy : TopCat.Homotopy (pair f g) (escaped f w) where
  toFun z := (f z.2, point z.1 (g z.2) (w z.2) (hgw z.2))
  continuous_toFun := by
    have hs : Continuous (fun z : ClosedInterval × X => (z.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
    have hg : Continuous (fun z : ClosedInterval × X => (g z.2 : Ambient n)) :=
      continuous_subtype_val.comp (g.hom.continuous.comp continuous_snd)
    have hw : Continuous (fun z : ClosedInterval × X => (w z.2 : Ambient n)) :=
      continuous_subtype_val.comp (w.hom.continuous.comp continuous_snd)
    have hb : Continuous (fun z : ClosedInterval × X => blend z.1 (g z.2) (w z.2)) :=
      ((continuous_const.sub hs).smul hg).add (hs.smul hw)
    have hi := hb.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (blend_ne_zero z.1 (g z.2) (w z.2) (hgw z.2)))
    have hp : Continuous (fun z : ClosedInterval × X => point z.1 (g z.2) (w z.2) (hgw z.2)) :=
      (hi.smul hb).subtype_mk _
    exact (f.hom.continuous.comp continuous_snd).prodMk hp
  map_zero_left x := Prod.ext rfl (point_zero (g x) (w x) (hgw x))
  map_one_left x := Prod.ext rfl (point_one (g x) (w x) (hgw x))

include hfw in
theorem homotopy_far {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (s : ClosedInterval) (x : X)
    (hx : ρ ≤ ‖(g x : Ambient n) - f x‖) :
    ρ ≤ ‖((homotopy f g w hgw) (s, x)).2.val - ((homotopy f g w hgw) (s, x)).1.val‖ :=
  far_preserved s (f x) (g x) (w x) (hgw x) (hfw x) hρ hρ1 hx

end
end Finsler.OrthogonalSphereEscape
