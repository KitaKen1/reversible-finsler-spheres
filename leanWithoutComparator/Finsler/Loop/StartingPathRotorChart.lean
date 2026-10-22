module

public import Finsler.Loop.TimedRotorPathMap
public import Finsler.Loop.StartingPathSphereCover

/-! An actual HOMEOMORPHISM for each endpoint-puncture patch of
the starting-point path space. A time-dependent orthogonal field
fixes the start and identifies the endpoint with the chart pole;
no path concatenation or uninstantiated fibration theorem is used. -/
@[expose] public section
namespace Finsler.StartingPathRotorChart
open CategoryTheory Topology
open Finsler.SphereGeometry Finsler.H1PuncturedEvaluationChart
open Finsler.StartingPathSphereCover Finsler.TimedRotorPathMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
local notation "I" => _root_.unitInterval

def endpointBase {n : ℕ} (x a : Sphere n) (p : patch x a) : base a := ⟨p.val.val 1, p.property⟩

theorem endpointBase_continuous {n : ℕ} (x a : Sphere n) : Continuous (endpointBase x a) :=
  ((continuous_eval_const 1).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

def forwardPath {n : ℕ} (x a : Sphere n) (p : patch x a) : Path x a where
  toContinuousMap := rotated a (endpointBase x a p) p.val.val
  source' := (rotated_zero a _ _).trans p.val.property
  target' := rotated_one a _ _ rfl

def forward {n : ℕ} (x a : Sphere n) (p : patch x a) : base a × Path x a :=
  (endpointBase x a p, forwardPath x a p)

def inversePath {n : ℕ} (x a : Sphere n) (p : base a × Path x a) : StartingPathSphereCover.total x :=
  ⟨unrotated a p.1 p.2.toContinuousMap, (unrotated_zero a _ _).trans p.2.source⟩

theorem inverse_endpoint {n : ℕ} (x a : Sphere n) (p : base a × Path x a) :
    (inversePath x a p).val 1 = p.1.val := unrotated_one a p.1 p.2.toContinuousMap p.2.target

def inverse {n : ℕ} (x a : Sphere n) (p : base a × Path x a) : patch x a :=
  ⟨inversePath x a p, by
    change (inversePath x a p).val 1 ∈ base a
    rw [inverse_endpoint]
    exact p.1.property⟩

theorem inverse_forward {n : ℕ} (x a : Sphere n) (p : patch x a) : inverse x a (forward x a p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact unrotated_rotated a (endpointBase x a p) p.val.val

theorem forward_inverse {n : ℕ} (x a : Sphere n) (p : base a × Path x a) : forward x a (inverse x a p) = p := by
  apply Prod.ext
  · exact Subtype.ext (inverse_endpoint x a p)
  · apply Path.ext
    funext t
    change TimedRotorPunctured.sphereMap
      (RotorHomotopy.path t ((inversePath x a p).val 1 : Ambient n) (a : Ambient n))
      (TimedRotorPunctured.sphereMap (RotorHomotopy.path t (p.1.val : Ambient n) (a : Ambient n)).symm
        (p.2 t)) = p.2 t
    rw [inverse_endpoint]
    exact TimedRotorPunctured.sphereMap_apply_symm _ _

theorem continuous_forward {n : ℕ} (x a : Sphere n) : Continuous (forward x a) := by
  have hp : Continuous (fun p : patch x a => p.val.val) := continuous_subtype_val.comp continuous_subtype_val
  have hr := (rotated_continuous a).comp ((endpointBase_continuous x a).prodMk hp)
  have hpath : Continuous (forwardPath x a) := continuous_induced_rng.mpr hr
  exact (endpointBase_continuous x a).prodMk hpath

theorem continuous_inverse {n : ℕ} (x a : Sphere n) : Continuous (inverse x a) := by
  have hp : Continuous (fun p : base a × Path x a => p.2.toContinuousMap) :=
    continuous_induced_dom.comp continuous_snd
  have hr := (unrotated_continuous a).comp (continuous_fst.prodMk hp)
  exact (hr.subtype_mk _).subtype_mk _

def homeomorph {n : ℕ} (x a : Sphere n) : patch x a ≃ₜ (base a × Path x a) where
  toFun := forward x a
  invFun := inverse x a
  left_inv := inverse_forward x a
  right_inv := forward_inverse x a
  continuous_toFun := continuous_forward x a
  continuous_invFun := continuous_inverse x a

def fixedForward {n : ℕ} (x a : Sphere n) (z : base a) (p : Path x z.val) : Path x a where
  toContinuousMap := rotated a z p.toContinuousMap
  source' := (rotated_zero a z _).trans p.source
  target' := rotated_one a z _ p.target

def fixedInverse {n : ℕ} (x a : Sphere n) (z : base a) (p : Path x a) : Path x z.val where
  toContinuousMap := unrotated a z p.toContinuousMap
  source' := (unrotated_zero a z _).trans p.source
  target' := unrotated_one a z _ p.target

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem continuous_fixedForward {n : ℕ} (x a : Sphere n) (z : base a) : Continuous (fixedForward x a z) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Path x z.val => rotated a z p.toContinuousMap)
  have hf : Continuous (fun p : Path x z.val => (z, p.toContinuousMap)) :=
    continuous_const.prodMk continuous_induced_dom
  have hh := (rotated_continuous a).comp (f := fun p : Path x z.val => (z, p.toContinuousMap)) hf
  exact hh

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem continuous_fixedInverse {n : ℕ} (x a : Sphere n) (z : base a) : Continuous (fixedInverse x a z) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Path x a => unrotated a z p.toContinuousMap)
  have hf : Continuous (fun p : Path x a => (z, p.toContinuousMap)) :=
    continuous_const.prodMk continuous_induced_dom
  have hh := (unrotated_continuous a).comp (f := fun p : Path x a => (z, p.toContinuousMap)) hf
  exact hh

def fixedFiberHomeomorph {n : ℕ} (x a : Sphere n) (z : base a) : Path x z.val ≃ₜ Path x a where
  toFun := fixedForward x a z
  invFun := fixedInverse x a z
  left_inv p := by
    apply Path.ext
    funext t
    exact TimedRotorPunctured.sphereMap_symm_apply _ _
  right_inv p := by
    apply Path.ext
    funext t
    exact TimedRotorPunctured.sphereMap_apply_symm _ _
  continuous_toFun := continuous_fixedForward x a z
  continuous_invFun := continuous_fixedInverse x a z

end
end Finsler.StartingPathRotorChart
