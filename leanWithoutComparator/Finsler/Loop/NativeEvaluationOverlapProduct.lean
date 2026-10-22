module

public import Finsler.Loop.NativeEvaluationMayerVietoris
public import Finsler.Loop.H1PuncturedPatchHomology

/-! Identify the ACTUAL full-loop overlap with the actual two-pole
complement times the genuine strong-H1 based loop space. Preserve
the original overlap evaluation and actual northern chart alignment. -/
@[expose] public section
namespace Finsler.NativeEvaluationOverlapProduct
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.H1LocalFiber (based)
open Finsler.H1FiberBase Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy
open Finsler.H1PuncturedEvaluationChart Finsler.H1PuncturedRelativeChart
open Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

abbrev model {n : ℕ} (y : Sphere n) : TopCat.{0} := TopCat.of (baseOverlap y × based y)

def forward {n : ℕ} (y : Sphere n) (u : overlap y) : model y :=
  (⟨point u.val.val, u.property⟩, ⟨align u.val.val y, basepoint_align u.val.val y⟩)

def inverse {n : ℕ} (y : Sphere n) (p : model y) : overlap y :=
  ⟨⟨align p.2.val p.1.val, Set.mem_univ _⟩, by
    change point (align p.2.val p.1.val) ∈ base y ∩ base (MeridianLoopFamily.antipode y)
    rw [point_align]
    exact p.1.property⟩

theorem inverse_forward {n : ℕ} (y : Sphere n) (u : overlap y) : inverse y (forward y u) = u := by
  apply Subtype.ext
  apply Subtype.ext
  exact align_reverse u.val.val y

theorem forward_inverse {n : ℕ} (y : Sphere n) (p : model y) : forward y (inverse y p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact point_align p.2.val p.1.val
  · apply Subtype.ext
    have he : point p.2.val = y := Subtype.ext p.2.property
    change align (align p.2.val p.1.val) y = p.2.val
    simpa only [he] using align_reverse p.2.val p.1.val

theorem continuous_forward {n : ℕ} (y : Sphere n) : Continuous (forward y) := by
  have hu : Continuous (fun u : overlap y => u.val.val) := continuous_subtype_val.comp continuous_subtype_val
  have hp := continuous_point.comp hu
  have hc := align_continuous (fun u : overlap y => u.val.val) (fun _ => y) hu continuous_const
    (fun u => sum_ne_zero (point u.val.val) y u.property.1)
  exact (hp.subtype_mk _).prodMk (hc.subtype_mk _)

theorem continuous_inverse {n : ℕ} (y : Sphere n) : Continuous (inverse y) := by
  have hu : Continuous (fun p : model y => p.2.val) := continuous_snd.subtype_val
  have hx : Continuous (fun p : model y => p.1.val) := continuous_fst.subtype_val
  have hc := align_continuous (fun p : model y => p.2.val) (fun p => p.1.val) hu hx (by
    intro p
    rw [p.2.property, add_comm]
    exact sum_ne_zero p.1.val y p.1.property.1)
  exact (hc.subtype_mk _).subtype_mk _

def homeomorph {n : ℕ} (y : Sphere n) : overlap y ≃ₜ model y where
  toFun := forward y
  invFun := inverse y
  left_inv := inverse_forward y
  right_inv := forward_inverse y
  continuous_toFun := continuous_forward y
  continuous_invFun := continuous_inverse y

def iso {n : ℕ} (y : Sphere n) : overlap y ≅ model y := TopCat.isoOfHomeo (homeomorph y)

def baseProjection {n : ℕ} (y : Sphere n) : model y ⟶ baseOverlap y :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

def fiberProjection {n : ℕ} (y : Sphere n) : model y ⟶ TopCat.of (based y) :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

def northInclusion {n : ℕ} (y : Sphere n) : overlap y ⟶ TopCat.of (fullDomain y) :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)

def northAlignment {n : ℕ} (y : Sphere n) : TopCat.of (fullDomain y) ⟶ TopCat.of (based y) :=
  TopCat.ofHom ⟨(H1PuncturedRelativeChart.fullDomainHomeomorph y).symm,
    (H1PuncturedRelativeChart.fullDomainHomeomorph y).symm.continuous⟩ ≫
    TopCat.ofHom (H1PuncturedPatchHomology.patchEquiv y).toFun

theorem evaluation_factor {n : ℕ} (y : Sphere n) :
    (iso y).hom ≫ baseProjection y = overlapEvaluation y := by ext u : 1; rfl

theorem alignment_factor {n : ℕ} (y : Sphere n) :
    (iso y).hom ≫ fiberProjection y = northInclusion y ≫ northAlignment y := by
  ext u : 1
  apply Subtype.ext
  rfl

end
end Finsler.NativeEvaluationOverlapProduct
