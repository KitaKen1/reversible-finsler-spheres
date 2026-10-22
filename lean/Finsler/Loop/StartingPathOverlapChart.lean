module

public import Finsler.Loop.StartingPathRotorChart
public import Finsler.Loop.NativeEvaluationConnectedFiber

/-! The actual two-puncture starting-path overlap is homeomorphic
to the actual base overlap times Path(start,north pole). Keep the
literal actual fixed-fiber map and its factorization through a true
fixed-end path-space homeomorphism and a true product section. -/
@[expose] public section
namespace Finsler.StartingPathOverlapChart
open CategoryTheory Topology
open Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.H1PuncturedEvaluationChart Finsler.StartingPathSphereCover
open Finsler.TimedRotorPathMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

abbrev model {n : ℕ} (x a : Sphere n) : TopCat.{0} :=
  ProductHomologyZeroDetection.product (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a))

def forward {n : ℕ} (x a : Sphere n) (p : overlap x a) : model x a :=
  (⟨p.val.val 1, p.property⟩, StartingPathRotorChart.forwardPath x a (north x a p))

def inverse {n : ℕ} (x a : Sphere n) (p : model x a) : overlap x a :=
  ⟨StartingPathRotorChart.inversePath x a (⟨p.1.val, p.1.property.1⟩, p.2), by
    change (StartingPathRotorChart.inversePath x a (⟨p.1.val, p.1.property.1⟩, p.2)).val 1 ∈ base a ∩ base (antipode a)
    rw [StartingPathRotorChart.inverse_endpoint]
    exact p.1.property⟩

theorem inverse_forward {n : ℕ} (x a : Sphere n) (p : overlap x a) : inverse x a (forward x a p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact unrotated_rotated a ⟨p.val.val 1, p.property.1⟩ p.val.val

theorem forward_inverse {n : ℕ} (x a : Sphere n) (p : model x a) : forward x a (inverse x a p) = p := by
  apply Prod.ext
  · exact Subtype.ext (StartingPathRotorChart.inverse_endpoint x a (⟨p.1.val, p.1.property.1⟩, p.2))
  · apply Path.ext
    funext t
    change TimedRotorPunctured.sphereMap
      (RotorHomotopy.path t ((StartingPathRotorChart.inversePath x a
        (⟨p.1.val, p.1.property.1⟩, p.2)).val 1 : Ambient n) (a : Ambient n))
      (TimedRotorPunctured.sphereMap (RotorHomotopy.path t (p.1.val : Ambient n) (a : Ambient n)).symm
        (p.2 t)) = p.2 t
    rw [StartingPathRotorChart.inverse_endpoint]
    exact TimedRotorPunctured.sphereMap_apply_symm _ _

theorem continuous_forward {n : ℕ} (x a : Sphere n) : Continuous (forward x a) := by
  have hb : Continuous (fun p : overlap x a => (⟨p.val.val 1, p.property⟩ : NativeEvaluationMayerVietoris.baseOverlap a)) :=
    ((continuous_eval_const 1).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hp := continuous_snd.comp ((StartingPathRotorChart.homeomorph x a).continuous.comp
    (north x a).hom.continuous)
  exact hb.prodMk hp

theorem continuous_inverse {n : ℕ} (x a : Sphere n) : Continuous (inverse x a) := by
  have hb : Continuous (fun p : model x a => (⟨p.1.val, p.1.property.1⟩ : base a)) :=
    continuous_fst.subtype_val.subtype_mk _
  have hp := (StartingPathRotorChart.homeomorph x a).symm.continuous.comp (hb.prodMk continuous_snd)
  exact hp.subtype_val.subtype_mk _

def homeomorph {n : ℕ} (x a : Sphere n) : overlap x a ≃ₜ model x a where
  toFun := forward x a
  invFun := inverse x a
  left_inv := inverse_forward x a
  right_inv := forward_inverse x a
  continuous_toFun := continuous_forward x a
  continuous_invFun := continuous_inverse x a

def iso {n : ℕ} (x a : Sphere n) : overlap x a ≅ model x a := TopCat.isoOfHomeo (homeomorph x a)

theorem fixed_fiber_square {n : ℕ} (x a z : Sphere n) (hz : z ∈ base a ∩ base (antipode a)) :
    fiberToOverlap x a z hz ≫ (iso x a).hom =
      (TopCat.isoOfHomeo (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨z, hz.1⟩)).hom ≫
        ProductHomologyDetectionTransport.fiberSection (NativeEvaluationMayerVietoris.baseOverlap a)
          (TopCat.of (Path x a)) ⟨z, hz⟩ := by
  ext p : 1
  apply Prod.ext
  · exact Subtype.ext p.target
  · apply Path.ext
    funext t
    change TimedRotorPunctured.sphereMap (RotorHomotopy.path t (p 1 : Ambient n) (a : Ambient n)) (p t) =
      TimedRotorPunctured.sphereMap (RotorHomotopy.path t (z : Ambient n) (a : Ambient n)) (p t)
    rw [p.target]

end
end Finsler.StartingPathOverlapChart
