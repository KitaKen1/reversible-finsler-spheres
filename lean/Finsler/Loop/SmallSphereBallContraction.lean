module

public import Finsler.Loop.CloseSphereHomotopy

/-! A REAL strong contraction of the explicit spherical chord ball
of radius one-third. The ORIGINAL normalized affine homotopy does
not increase its chord distance to the center. All normalizations
are actually nonzero. Any two points stay in the real distance<1 tube. -/
@[expose] public section
namespace Finsler.SmallSphereBallContraction
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def blend {n : ℕ} (s : _root_.unitInterval) (x Q : Sphere n) : Ambient n :=
  (1 - (s : ℝ)) • (x : Ambient n) + (s : ℝ) • (Q : Ambient n)

theorem blend_norm_le_one {n : ℕ} (s : _root_.unitInterval) (x Q : Sphere n) : ‖blend s x Q‖ ≤ 1 := by
  have he := norm_add_le ((1 - (s : ℝ)) • (x : Ambient n)) ((s : ℝ) • (Q : Ambient n))
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr s.property.2),
    Real.norm_of_nonneg s.property.1, mem_sphere_zero_iff_norm.mp x.property,
    mem_sphere_zero_iff_norm.mp Q.property, mul_one, mul_one] at he
  exact he.trans_eq (by ring)

theorem close_inner_pos {n : ℕ} (x Q : Sphere n) (h : ‖(x : Ambient n) - (Q : Ambient n)‖ < 1) :
    0 < ⟪(x : Ambient n), (Q : Ambient n)⟫ := by
  have he := norm_sub_sq_real (x : Ambient n) (Q : Ambient n)
  rw [mem_sphere_zero_iff_norm.mp x.property, mem_sphere_zero_iff_norm.mp Q.property] at he
  nlinarith [norm_nonneg ((x : Ambient n) - (Q : Ambient n))]

theorem blend_inner_ge {n : ℕ} (s : _root_.unitInterval) (x Q : Sphere n) :
    ⟪(x : Ambient n), (Q : Ambient n)⟫ ≤ ⟪blend s x Q, (Q : Ambient n)⟫ := by
  have he := real_inner_le_norm (x : Ambient n) (Q : Ambient n)
  rw [mem_sphere_zero_iff_norm.mp x.property, mem_sphere_zero_iff_norm.mp Q.property, mul_one] at he
  rw [blend, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp Q.property]
  nlinarith [mul_nonneg s.property.1 (sub_nonneg.mpr he)]

theorem normalized_inner_ge {n : ℕ} (s : _root_.unitInterval) (x Q : Sphere n)
    (h : ‖(x : Ambient n) - (Q : Ambient n)‖ < 1) :
    ⟪(x : Ambient n), (Q : Ambient n)⟫ ≤
      ⟪(SphereRetraction.normalize (blend s x Q) : Ambient n), (Q : Ambient n)⟫ := by
  have hd : dist x Q < 1 := by simpa only [Subtype.dist_eq, dist_eq_norm] using h
  have hnz : blend s x Q ≠ 0 := CloseSphereHomotopy.blend_ne_zero s x Q hd
  have hn : 0 < ‖blend s x Q‖ := norm_pos_iff.mpr hnz
  have hc := congrArg Subtype.val (SphereRetraction.normalize_coe ⟨blend s x Q, hnz⟩)
  change (SphereRetraction.normalize (blend s x Q) : Ambient n) = ‖blend s x Q‖⁻¹ • blend s x Q at hc
  rw [hc, real_inner_smul_left]
  rw [mul_comm (‖blend s x Q‖⁻¹), ← div_eq_mul_inv]
  apply (le_div_iff₀ hn).mpr
  exact (mul_le_of_le_one_right (close_inner_pos x Q h).le (blend_norm_le_one s x Q)).trans (blend_inner_ge s x Q)

theorem distance_nonincreasing {n : ℕ} (s : _root_.unitInterval) (x Q : Sphere n)
    (h : ‖(x : Ambient n) - (Q : Ambient n)‖ < 1) :
    ‖(SphereRetraction.normalize (blend s x Q) : Ambient n) - (Q : Ambient n)‖ ≤
      ‖(x : Ambient n) - (Q : Ambient n)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_sub_sq_real,
    mem_sphere_zero_iff_norm.mp (SphereRetraction.normalize (blend s x Q)).property,
    mem_sphere_zero_iff_norm.mp Q.property, mem_sphere_zero_iff_norm.mp x.property]
  nlinarith [normalized_inner_ge s x Q h]

def ball {n : ℕ} (Q : Sphere n) : Set (BorelEvaluation.sphere n) :=
  {x | ‖(x : Ambient n) - (Q : Ambient n)‖ < 1 / 3}
abbrev space {n : ℕ} (Q : Sphere n) : TopCat.{0} := TopCat.of (ball Q)

theorem ball_open {n : ℕ} (Q : Sphere n) : IsOpen (ball Q) :=
  isOpen_lt ((continuous_subtype_val.sub continuous_const).norm) continuous_const

def center {n : ℕ} (Q : Sphere n) : space Q := ⟨Q, by simp [ball]⟩
def inclusion {n : ℕ} (Q : Sphere n) : space Q ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
def constant {n : ℕ} (Q : Sphere n) : space Q ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom (ContinuousMap.const (space Q) Q)
def ambientHomotopy {n : ℕ} (Q : Sphere n) : TopCat.Homotopy (inclusion Q) (constant Q) :=
  CloseSphereHomotopy.homotopy (inclusion Q) (constant Q) (fun x => by
    change dist x.val Q < 1
    have hx := x.property
    change ‖(x.val : Ambient n) - (Q : Ambient n)‖ < 1 / 3 at hx
    simpa only [Subtype.dist_eq, dist_eq_norm] using hx.trans (by norm_num : (1 / 3 : ℝ) < 1))

theorem ambient_stays {n : ℕ} (Q : Sphere n) (s : _root_.unitInterval) (x : space Q) :
    ambientHomotopy Q (s, x) ∈ ball Q := by
  have hx := x.property
  have hb : ‖(x.val : Ambient n) - (Q : Ambient n)‖ < 1 := hx.trans (by norm_num : (1 / 3 : ℝ) < 1)
  exact (distance_nonincreasing s x.val Q hb).trans_lt hx

def contraction {n : ℕ} (Q : Sphere n) :
    TopCat.Homotopy (𝟙 (space Q)) (TopCat.ofHom (ContinuousMap.const (space Q) (center Q))) where
  toFun z := ⟨ambientHomotopy Q z, ambient_stays Q z.1 z.2⟩
  continuous_toFun := (ambientHomotopy Q).continuous.subtype_mk _
  map_zero_left x := by apply Subtype.ext; exact (ambientHomotopy Q).map_zero_left x
  map_one_left x := by apply Subtype.ext; exact (ambientHomotopy Q).map_one_left x

theorem contraction_fixed {n : ℕ} (Q : Sphere n) (s : _root_.unitInterval) :
    contraction Q (s, center Q) = center Q := by
  apply Subtype.ext
  exact CloseSphereHomotopy.fixed (inclusion Q) (constant Q) _ (center Q) rfl s

theorem pair_distance {n : ℕ} (Q : Sphere n) (x y : space Q) :
    ‖(y.val : Ambient n) - (x.val : Ambient n)‖ < 2 / 3 := by
  have he := norm_sub_le ((y.val : Ambient n) - Q) ((x.val : Ambient n) - Q)
  have hh : ((y.val : Ambient n) - Q) - ((x.val : Ambient n) - Q) = (y.val : Ambient n) - x.val := by abel
  rw [hh] at he
  have hx : ‖(x.val : Ambient n) - Q‖ < 1 / 3 := x.property
  have hy : ‖(y.val : Ambient n) - Q‖ < 1 / 3 := y.property
  linarith

theorem pair_tube {n : ℕ} (Q : Sphere n) (x y : space Q) :
    ‖(y.val : Ambient n) - (x.val : Ambient n)‖ < 1 :=
  (pair_distance Q x y).trans (by norm_num)

theorem quarter_inside {n : ℕ} (Q x : Sphere n)
    (h : ‖(x : Ambient n) - (Q : Ambient n)‖ ≤ 1 / 4) : x ∈ ball Q := by
  change _ < 1 / 3
  linarith

end
end Finsler.SmallSphereBallContraction
