module

public import Finsler.Loop.MeridianEquatorHomology
public import Finsler.Geometry.DiagonalGeometry

/-! An ACTUAL continuous unit vector perpendicular to the common
meridian plane over a hemisphere of equator directions. A genuine
third unit axis exists for n>=2. Orthogonal projection of that axis
never vanishes on the specified hemisphere; no tangent field on the
whole sphere or global trivialization is postulated. -/
@[expose] public section
namespace Finsler.MeridianTransverseField
open CategoryTheory Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.MeridianEquatorHomology Finsler.DiagonalGeometry
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem axis_exists {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) :
    ∃ w : equator P, ⟪(v₀.val : Ambient n), (w.val : Ambient n)⟫ = 0 := by
  let V := orthogonalSpace P
  let v : V := (toOrthogonal P v₀).val
  let K : Submodule ℝ V := (ℝ ∙ v)ᗮ
  have hd : Module.finrank ℝ V = (n - 1) + 1 := by
    rw [orthogonal_dimension P]
    omega
  let : Fact (Module.finrank ℝ V = (n - 1) + 1) := ⟨hd⟩
  have hv : v ≠ 0 := by
    exact ne_zero_of_mem_unit_sphere (toOrthogonal P v₀)
  have hK : Module.finrank ℝ K = n - 1 := Submodule.finrank_orthogonal_span_singleton hv
  let : Nontrivial K := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ K)
  obtain ⟨w⟩ := (NormedSpace.sphere_nonempty (E := K) (x := 0)).mpr zero_le_one |>.coe_sort
  let u : orthogonalSphere P := ⟨w.val.val, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact mem_sphere_zero_iff_norm.mp w.property⟩
  refine ⟨fromOrthogonal P u, ?_⟩
  have hw : ⟪v, w.val.val⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.val.property
  exact hw

def axis {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) : equator P :=
  (axis_exists hn P v₀).choose

theorem axis_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) :
    ⟪(v₀.val : Ambient n), ((axis hn P v₀).val : Ambient n)⟫ = 0 := (axis_exists hn P v₀).choose_spec

def hemisphere {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (equator P) :=
  {v | 0 < ⟪(v.val : Ambient n), (v₀.val : Ambient n)⟫}
abbrev space {n : ℕ} (P : Sphere n) (v₀ : equator P) := TopCat.of (hemisphere P v₀)

def projection {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ v : equator P) : Ambient n :=
  ((axis hn P v₀).val : Ambient n) -
    ⟪((axis hn P v₀).val : Ambient n), (v.val : Ambient n)⟫ • (v.val : Ambient n)

theorem projection_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ v : equator P) :
    ⟪(v.val : Ambient n), projection hn P v₀ v⟫ = 0 := by
  rw [projection, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, sphere_norm,
    ← real_inner_comm (v.val : Ambient n) ((axis hn P v₀).val : Ambient n)]
  ring

theorem projection_pole_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ v : equator P) :
    ⟪(P : Ambient n), projection hn P v₀ v⟫ = 0 := by
  rw [projection, inner_sub_right, real_inner_smul_right, (axis hn P v₀).property, v.property]
  ring

theorem projection_ne_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P)
    (v : hemisphere P v₀) : projection hn P v₀ v.val ≠ 0 := by
  intro hz
  have he := congrArg (fun a : Ambient n => ⟪(v₀.val : Ambient n), a⟫) hz
  rw [projection, inner_sub_right, real_inner_smul_right, axis_perp, inner_zero_right] at he
  have hv : 0 < ⟪(v₀.val : Ambient n), (v.val.val : Ambient n)⟫ := by
    rw [real_inner_comm]
    exact v.property
  have hc : ⟪((axis hn P v₀).val : Ambient n), (v.val.val : Ambient n)⟫ = 0 := by
    nlinarith
  have ha : ((axis hn P v₀).val : Ambient n) = 0 := by
    simpa only [projection, hc, zero_smul, sub_zero] using hz
  exact ne_zero_of_mem_unit_sphere (axis hn P v₀).val ha

def field {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (v : hemisphere P v₀) : Sphere n :=
  DiagonalGeometry.normalize (projection hn P v₀ v.val) (projection_ne_zero hn P v₀ v)

theorem field_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (v : hemisphere P v₀) :
    ⟪(v.val.val : Ambient n), (field hn P v₀ v : Ambient n)⟫ = 0 := by
  change ⟪(v.val.val : Ambient n), ‖projection hn P v₀ v.val‖⁻¹ • projection hn P v₀ v.val⟫ = 0
  rw [real_inner_smul_right, projection_perp, mul_zero]

theorem field_pole_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (v : hemisphere P v₀) :
    ⟪(P : Ambient n), (field hn P v₀ v : Ambient n)⟫ = 0 := by
  change ⟪(P : Ambient n), ‖projection hn P v₀ v.val‖⁻¹ • projection hn P v₀ v.val⟫ = 0
  rw [real_inner_smul_right, projection_pole_perp, mul_zero]

theorem field_continuous {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) :
    Continuous (field hn P v₀) := by
  have hv : Continuous (fun v : hemisphere P v₀ => (v.val.val : Ambient n)) := by fun_prop
  have ha : Continuous (fun _ : hemisphere P v₀ => ((axis hn P v₀).val : Ambient n)) := continuous_const
  have hi : Continuous (fun v : hemisphere P v₀ => ⟪((axis hn P v₀).val : Ambient n), (v.val.val : Ambient n)⟫) :=
    ha.inner hv
  have hp : Continuous (fun v : hemisphere P v₀ => projection hn P v₀ v.val) :=
    ha.sub (hi.smul hv)
  have hi := hp.norm.inv₀ (fun v => norm_ne_zero_iff.mpr (projection_ne_zero hn P v₀ v))
  exact (hi.smul hp).subtype_mk _

def map {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) : space P v₀ ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨field hn P v₀, field_continuous hn P v₀⟩

end
end Finsler.MeridianTransverseField
