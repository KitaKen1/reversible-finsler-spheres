module

public import Finsler.Loop.RationalNorthMeridianChart
public import Finsler.Loop.NativeMeridianPairCoordinates

/-! The ACTUAL full-meridian parameter map, restricted to the true
preimage of north-minus-pole, is a homeomorphism. The inverse rescales
the EXISTING rational outgoing chart time by onehalf. This is the
local coordinate isomorphism needed for support-pair excision. -/
@[expose] public section
namespace Finsler.MeridianNorthParameterChart
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.RationalSphereArc Finsler.RationalSphereArcCoordinates
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def northSet {n : ℕ} (P : Sphere n) : Set (BorelEvaluation.sphere n) :=
  {y | 0 < ⟪(P : Ambient n), (y : Ambient n)⟫ ∧ y ≠ P}
abbrev parameterSpace {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (_root_.unitInterval × equator P)
abbrev evaluation {n : ℕ} (P : Sphere n) := NativeMeridianPairCoordinates.meridianEvaluation P
def sourceSet {n : ℕ} (P : Sphere n) : Set (parameterSpace P) := evaluation P ⁻¹' northSet P

def halfTime (u : Set.Ioo (0 : ℝ) 1) : _root_.unitInterval :=
  ⟨(u : ℝ) / 2, by constructor <;> linarith [u.property.1, u.property.2]⟩

theorem half_value {n : ℕ} (P : Sphere n) (v : equator P) (u : Set.Ioo (0 : ℝ) 1) :
    meridian P v (halfTime u) = (RationalNorthMeridianChart.forward P (v, u)).val := by
  rw [← Path.extend_apply _ (halfTime u).property, meridian,
    Path.extend_trans_of_le_half _ _ (by change (u : ℝ) / 2 ≤ 1 / 2; linarith [u.property.2])]
  change (arc (outgoing P v)).extend (2 * ((u : ℝ) / 2)) = _
  rw [show 2 * ((u : ℝ) / 2) = (u : ℝ) by ring]
  exact Path.extend_apply (arc (outgoing P v)) (RationalNorthMeridianChart.intervalTime u).property

theorem time_lt_half {n : ℕ} (P : Sphere n) (v : equator P) (t : _root_.unitInterval)
    (hnorth : 0 < ⟪(P : Ambient n), (meridian P v t : Ambient n)⟫) : (t : ℝ) < 1 / 2 := by
  by_contra ht
  have hhalf : (1 / 2 : ℝ) ≤ (t : ℝ) := le_of_not_gt ht
  let u : _root_.unitInterval := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.2]⟩
  have he : meridian P v t = point (incoming P v) u := by
    rw [← Path.extend_apply _ t.property, meridian, Path.extend_trans_of_half_le _ _ hhalf]
    exact Path.extend_apply (arc (incoming P v)) u.property
  rw [he, coordinates] at hnorth
  change 0 < ⟪(P : Ambient n), alpha u • (v.val : Ambient n) + beta u • (-(P : Ambient n))⟫ at hnorth
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, v.property, inner_neg_right,
    real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp P.property] at hnorth
  nlinarith [beta_nonneg u]

theorem time_pos {n : ℕ} (P : Sphere n) (v : equator P) (t : _root_.unitInterval)
    (hne : meridian P v t ≠ P) : 0 < (t : ℝ) := by
  by_contra ht
  have hz : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
  exact hne (hz ▸ (meridian P v).source)

def forward {n : ℕ} (P : Sphere n) (z : sourceSet P) : RationalNorthMeridianChart.north P :=
  ⟨evaluation P z.val, z.property⟩

def inverse {n : ℕ} (P : Sphere n) (y : RationalNorthMeridianChart.north P) : sourceSet P :=
  ⟨(halfTime (RationalNorthMeridianChart.inverse P y).2, (RationalNorthMeridianChart.inverse P y).1), by
    change meridian P (RationalNorthMeridianChart.inverse P y).1
      (halfTime (RationalNorthMeridianChart.inverse P y).2) ∈ northSet P
    rw [half_value, show (RationalNorthMeridianChart.forward P (RationalNorthMeridianChart.inverse P y)).val = y.val from
      congrArg Subtype.val (RationalNorthMeridianChart.forward_inverse P y)]
    exact y.property⟩

theorem forward_inverse {n : ℕ} (P : Sphere n) (y : RationalNorthMeridianChart.north P) :
    forward P (inverse P y) = y := by
  apply Subtype.ext
  exact (half_value P _ _).trans (congrArg Subtype.val (RationalNorthMeridianChart.forward_inverse P y))

theorem inverse_forward {n : ℕ} (P : Sphere n) (z : sourceSet P) : inverse P (forward P z) = z := by
  let u : Set.Ioo (0 : ℝ) 1 := ⟨2 * (z.val.1 : ℝ), by
    constructor
    · linarith [time_pos P z.val.2 z.val.1 z.property.2]
    · linarith [time_lt_half P z.val.2 z.val.1 z.property.1]⟩
  have ht : halfTime u = z.val.1 := by apply Subtype.ext; change (2 * (z.val.1 : ℝ)) / 2 = _; ring
  have hf : forward P z = RationalNorthMeridianChart.forward P (z.val.2, u) := by
    apply Subtype.ext
    change meridian P z.val.2 z.val.1 = _
    rw [← ht]
    exact half_value P z.val.2 u
  have hi := RationalNorthMeridianChart.inverse_forward P (z.val.2, u)
  apply Subtype.ext
  change (halfTime (RationalNorthMeridianChart.inverse P (forward P z)).2,
    (RationalNorthMeridianChart.inverse P (forward P z)).1) = z.val
  rw [hf, hi, ht]

theorem continuous_forward {n : ℕ} (P : Sphere n) : Continuous (forward P) :=
  ((evaluation P).hom.continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_inverse {n : ℕ} (P : Sphere n) : Continuous (inverse P) := by
  have hu := continuous_snd.comp (RationalNorthMeridianChart.continuous_inverse P)
  have ht : Continuous (fun y : RationalNorthMeridianChart.north P =>
      halfTime (RationalNorthMeridianChart.inverse P y).2) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp hu).div_const 2
  have hd := continuous_fst.comp (RationalNorthMeridianChart.continuous_inverse P)
  exact (ht.prodMk hd).subtype_mk _

def homeomorph {n : ℕ} (P : Sphere n) : sourceSet P ≃ₜ RationalNorthMeridianChart.north P where
  toFun := forward P
  invFun := inverse P
  left_inv := inverse_forward P
  right_inv := forward_inverse P
  continuous_toFun := continuous_forward P
  continuous_invFun := continuous_inverse P

theorem sourceSet_open {n : ℕ} (P : Sphere n) : IsOpen (sourceSet P) :=
  (RationalNorthMeridianChart.north_isOpen P).preimage (evaluation P).hom.continuous

end
end Finsler.MeridianNorthParameterChart
