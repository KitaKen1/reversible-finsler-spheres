module

public import Finsler.Geometry.RationalSphereCurve
public import Mathlib.Topology.Path

/-! Genuine quarter-meridian paths for orthogonal unit sphere points.
The existing rational sphere curve gives exact endpoints and joint
continuity without trigonometric differentiation or normalization. -/

@[expose] public section
namespace Finsler.RationalSphereArc
open Topology Finsler.SphereGeometry Finsler.RationalSphereCurve
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

abbrev orthogonalPairs (n : ℕ) := {z : Sphere n × Sphere n // ⟪(z.1 : Ambient n), (z.2 : Ambient n)⟫ = 0}

def point {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) : Sphere n :=
  ⟨ratMap (2 * (t : ℝ)) ((z.val.1 : Ambient n), (z.val.2 : Ambient n)), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_ratMap (mem_sphere_zero_iff_norm.mp z.val.1.property) z.property⟩

theorem point_zero {n : ℕ} (z : orthogonalPairs n) : point z 0 = z.val.1 := by
  apply Subtype.ext
  change ratMap (2 * 0) ((z.val.1 : Ambient n), (z.val.2 : Ambient n)) = _
  rw [mul_zero, ratMap_zero]

theorem point_one {n : ℕ} (z : orthogonalPairs n) : point z 1 = z.val.2 := by
  apply Subtype.ext
  have hy := mem_sphere_zero_iff_norm.mp z.val.2.property
  change ratMap (2 * 1) ((z.val.1 : Ambient n), (z.val.2 : Ambient n)) = _
  norm_num [ratMap, aFun, hy, smul_smul]

theorem point_continuous (n : ℕ) :
    Continuous (fun zt : orthogonalPairs n × _root_.unitInterval => point zt.1 zt.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun zt : orthogonalPairs n × _root_.unitInterval =>
    (1 + aFun (2 * (zt.2 : ℝ)) (zt.1.val.2 : Ambient n))⁻¹ •
      ((1 - aFun (2 * (zt.2 : ℝ)) (zt.1.val.2 : Ambient n)) • (zt.1.val.1 : Ambient n) +
        (2 * (zt.2 : ℝ)) • (zt.1.val.2 : Ambient n)))
  have ha : Continuous (fun zt : orthogonalPairs n × _root_.unitInterval =>
      aFun (2 * (zt.2 : ℝ)) (zt.1.val.2 : Ambient n)) := by
    unfold aFun
    fun_prop
  apply ((continuous_const.add ha).inv₀ (fun zt => ?_)).smul
    (((continuous_const.sub ha).smul (by fun_prop)).add (by fun_prop))
  have h := aFun_nonneg (2 * (zt.2 : ℝ)) (zt.1.val.2 : Ambient n)
  change 1 + aFun (2 * (zt.2 : ℝ)) (zt.1.val.2 : Ambient n) ≠ 0
  linarith

def arc {n : ℕ} (z : orthogonalPairs n) : Path z.val.1 z.val.2 where
  toFun := point z
  continuous_toFun := (point_continuous n).comp (continuous_const.prodMk continuous_id)
  source' := point_zero z
  target' := point_one z

theorem family_continuous {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : X → orthogonalPairs n) (hf : Continuous f) :
    Continuous (fun xt : X × _root_.unitInterval => arc (f xt.1) xt.2) :=
  (point_continuous n).comp ((hf.comp continuous_fst).prodMk continuous_snd)

end
end Finsler.RationalSphereArc
