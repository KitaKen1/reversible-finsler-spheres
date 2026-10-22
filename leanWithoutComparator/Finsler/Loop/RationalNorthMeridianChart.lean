module

public import Finsler.Loop.H1RationalSphereArc
public import Finsler.Loop.MeridianInteriorDirection

/-! The ORIGINAL rational outgoing meridian is an actual chart:
equator times(0,1) is homeomorphic to the open northern hemisphere
with its pole removed. The explicit inverse uses the EXISTING
stereographic map, its norm/2, and its normalized direction. -/
@[expose] public section
namespace Finsler.RationalNorthMeridianChart
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.RationalSphereArc Finsler.RationalSphereCurve Finsler.RationalSphereArcCoordinates
open Finsler.SobolevSphereChart
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

abbrev north {n : ℕ} (P : Sphere n) :=
  {y : Sphere n // 0 < ⟪(P : Ambient n), (y : Ambient n)⟫ ∧ y ≠ P}
abbrev parameters {n : ℕ} (P : Sphere n) := equator P × Set.Ioo (0 : ℝ) 1

def intervalTime (t : Set.Ioo (0 : ℝ) 1) : _root_.unitInterval := ⟨t.val, t.property.1.le, t.property.2.le⟩

theorem stereo_point {n : ℕ} (P : Sphere n) (v : equator P) (t : _root_.unitInterval) :
    stereo (P : Ambient n) (point (outgoing P v) t : Ambient n) = (2 * (t : ℝ)) • (v.val : Ambient n) := by
  change stereo (P : Ambient n) (ratMap (2 * (t : ℝ)) ((P : Ambient n), (v.val : Ambient n))) = _
  rw [← H1RationalSphereArc.ratMap_scale]
  exact stereo_ratMap (mem_sphere_zero_iff_norm.mp P.property)
    (by rw [inner_smul_right, v.property, mul_zero])

def forward {n : ℕ} (P : Sphere n) (z : parameters P) : north P :=
  ⟨point (outgoing P z.1) (intervalTime z.2), by
    constructor
    · change 0 < ⟪(P : Ambient n), (point (outgoing P z.1) (intervalTime z.2) : Ambient n)⟫
      have he := RationalSphereArcCarrier.inner_left (outgoing P z.1) (intervalTime z.2)
      change ⟪(P : Ambient n), (point (outgoing P z.1) (intervalTime z.2) : Ambient n)⟫ = alpha (intervalTime z.2) at he
      rw [he]
      exact alpha_pos (intervalTime z.2) z.2.property.2
    · intro he
      have hs := stereo_point P z.1 (intervalTime z.2)
      rw [he] at hs
      have hz : stereo (P : Ambient n) (P : Ambient n) = 0 := by
        have hPP : ⟪(P : Ambient n), (P : Ambient n)⟫ = 1 := by
          rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp P.property]
          norm_num
        simp only [stereo, hPP, one_smul, sub_self, smul_zero]
      rw [hz] at hs
      have hn := congrArg norm hs
      rw [norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (by change 0 < 2 * (z.2 : ℝ); linarith [z.2.property.1]),
        mem_sphere_zero_iff_norm.mp z.1.val.property, mul_one] at hn
      change 0 = 2 * (z.2 : ℝ) at hn
      linarith [z.2.property.1]⟩

theorem continuous_forward {n : ℕ} (P : Sphere n) : Continuous (forward P) := by
  apply Continuous.subtype_mk
  have hp : Continuous (fun z : parameters P => outgoing P z.1) := by
    exact (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  have ht : Continuous (fun z : parameters P => intervalTime z.2) := by
    unfold intervalTime
    fun_prop
  have hc := (point_continuous n).comp (hp.prodMk ht)
  exact hc.congr (fun _ => rfl)

def coordinate {n : ℕ} (P : Sphere n) : C(north P, Ambient n) :=
  ⟨fun y => stereo (P : Ambient n) (y.val : Ambient n), by
    have hg : Continuous (fun y : north P => ⟪(y.val : Ambient n), (P : Ambient n)⟫) := by fun_prop
    change Continuous (fun y : north P =>
      (2 / (1 + ⟪(y.val : Ambient n), (P : Ambient n)⟫)) •
        ((y.val : Ambient n) - ⟪(y.val : Ambient n), (P : Ambient n)⟫ • (P : Ambient n)))
    have hden : ∀ y : north P, (1 : ℝ) + ⟪(y.val : Ambient n), (P : Ambient n)⟫ ≠ 0 := by
      intro y
      have hy := y.property.1
      rw [real_inner_comm] at hy
      linarith
    have hscale : Continuous (fun y : north P => (2 : ℝ) / (1 + ⟪(y.val : Ambient n), (P : Ambient n)⟫)) :=
      continuous_const.div (continuous_const.add hg) hden
    have hy : Continuous (fun y : north P => (y.val : Ambient n)) := by fun_prop
    exact hscale.smul (hy.sub (hg.smul continuous_const))⟩

theorem coordinate_ne_zero {n : ℕ} (P : Sphere n) (y : north P) : coordinate P y ≠ 0 := by
  intro he
  have hy : -1 < ⟪(y.val : Ambient n), (P : Ambient n)⟫ := by
    rw [real_inner_comm]
    linarith [y.property.1]
  have hi := ratMap_stereo (mem_sphere_zero_iff_norm.mp P.property)
    (mem_sphere_zero_iff_norm.mp y.val.property) hy
  change ratMap 1 ((P : Ambient n), coordinate P y) = (y.val : Ambient n) at hi
  rw [he] at hi
  have hz : ratMap 1 ((P : Ambient n), (0 : Ambient n)) = (P : Ambient n) := by
    simp [ratMap, aFun]
  rw [hz] at hi
  exact y.property.2 (Subtype.ext hi.symm)

theorem coordinate_norm_lt_two {n : ℕ} (P : Sphere n) (y : north P) : ‖coordinate P y‖ < 2 := by
  have hy : 0 < ⟪(y.val : Ambient n), (P : Ambient n)⟫ := by
    rw [real_inner_comm]
    exact y.property.1
  have hs := norm_sq_stereo (mem_sphere_zero_iff_norm.mp P.property)
    (mem_sphere_zero_iff_norm.mp y.val.property) (by linarith : -1 < ⟪(y.val : Ambient n), (P : Ambient n)⟫)
  have hq : ‖coordinate P y‖ ^ 2 < 4 := by
    change ‖stereo (P : Ambient n) (y.val : Ambient n)‖ ^ 2 < 4
    rw [hs]
    apply (div_lt_iff₀ (by linarith : 0 < 1 + ⟪(y.val : Ambient n), (P : Ambient n)⟫)).mpr
    linarith
  nlinarith [norm_nonneg (coordinate P y)]

def inverseDirection {n : ℕ} (P : Sphere n) (y : north P) : equator P :=
  ⟨⟨NormedSpace.normalize (coordinate P y), mem_sphere_zero_iff_norm.mpr
    (NormedSpace.norm_normalize (coordinate_ne_zero P y))⟩, by
    change ⟪(P : Ambient n), ‖coordinate P y‖⁻¹ • coordinate P y⟫ = 0
    rw [inner_smul_right, real_inner_comm]
    have hz := inner_stereo (z := (y.val : Ambient n)) (mem_sphere_zero_iff_norm.mp P.property)
    change ⟪coordinate P y, (P : Ambient n)⟫ = 0 at hz
    rw [hz, mul_zero]⟩

def inverseTime {n : ℕ} (P : Sphere n) (y : north P) : Set.Ioo (0 : ℝ) 1 :=
  ⟨‖coordinate P y‖ / 2, div_pos (norm_pos_iff.mpr (coordinate_ne_zero P y)) (by norm_num),
    (div_lt_one (by norm_num : (0 : ℝ) < 2)).mpr (coordinate_norm_lt_two P y)⟩

def inverse {n : ℕ} (P : Sphere n) (y : north P) : parameters P := (inverseDirection P y, inverseTime P y)

theorem continuous_inverse {n : ℕ} (P : Sphere n) : Continuous (inverse P) := by
  have hd : Continuous (inverseDirection P) := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun y : north P => ‖coordinate P y‖⁻¹ • coordinate P y)
    exact (((coordinate P).continuous.norm).inv₀ (fun y => norm_ne_zero_iff.mpr (coordinate_ne_zero P y))).smul
      (coordinate P).continuous
  have ht : Continuous (inverseTime P) :=
    ((coordinate P).continuous.norm.div_const 2).subtype_mk _
  exact hd.prodMk ht

theorem inverse_forward {n : ℕ} (P : Sphere n) (z : parameters P) : inverse P (forward P z) = z := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    change NormedSpace.normalize (stereo (P : Ambient n) (point (outgoing P z.1) (intervalTime z.2) : Ambient n)) = (z.1.val : Ambient n)
    rw [stereo_point, NormedSpace.normalize_smul_of_pos (by change 0 < 2 * (z.2 : ℝ); linarith [z.2.property.1]),
      NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp z.1.val.property)]
  · apply Subtype.ext
    change ‖stereo (P : Ambient n) (point (outgoing P z.1) (intervalTime z.2) : Ambient n)‖ / 2 = (z.2 : ℝ)
    rw [stereo_point, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by change 0 < 2 * (z.2 : ℝ); linarith [z.2.property.1]), mem_sphere_zero_iff_norm.mp z.1.val.property]
    change (2 * (z.2 : ℝ)) * 1 / 2 = (z.2 : ℝ)
    ring

theorem forward_inverse {n : ℕ} (P : Sphere n) (y : north P) : forward P (inverse P y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  change ratMap (2 * (‖coordinate P y‖ / 2)) ((P : Ambient n), NormedSpace.normalize (coordinate P y)) = (y.val : Ambient n)
  rw [← H1RationalSphereArc.ratMap_scale]
  rw [show 2 * (‖coordinate P y‖ / 2) = ‖coordinate P y‖ by ring, NormedSpace.norm_smul_normalize]
  exact ratMap_stereo (mem_sphere_zero_iff_norm.mp P.property) (mem_sphere_zero_iff_norm.mp y.val.property)
    (by rw [real_inner_comm]; linarith [y.property.1])

def homeomorph {n : ℕ} (P : Sphere n) : parameters P ≃ₜ north P where
  toFun := forward P
  invFun := inverse P
  left_inv := inverse_forward P
  right_inv := forward_inverse P
  continuous_toFun := continuous_forward P
  continuous_invFun := continuous_inverse P

theorem north_isOpen {n : ℕ} (P : Sphere n) :
    IsOpen {y : Sphere n | 0 < ⟪(P : Ambient n), (y : Ambient n)⟫ ∧ y ≠ P} := by
  have hi : Continuous (fun y : Sphere n => ⟪(P : Ambient n), (y : Ambient n)⟫) := by fun_prop
  exact (isOpen_lt continuous_const hi).inter (isClosed_singleton.isOpen_compl)

theorem isOpenEmbedding_forward {n : ℕ} (P : Sphere n) :
    Topology.IsOpenEmbedding (fun z : parameters P => (forward P z).val) :=
  (north_isOpen P).isOpenEmbedding_subtypeVal.comp (homeomorph P).isOpenEmbedding

end
end Finsler.RationalNorthMeridianChart
