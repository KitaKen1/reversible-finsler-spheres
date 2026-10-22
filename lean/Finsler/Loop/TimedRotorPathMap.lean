module

public import Finsler.Loop.TimedRotorPunctured

/-! Apply the genuine time-dependent orthogonal field to an entire
continuous sphere path. Forward and inverse are jointly continuous
in the endpoint parameter and the original compact-open path. -/
@[expose] public section
namespace Finsler.TimedRotorPathMap
open CategoryTheory Topology
open Finsler.SphereGeometry Finsler.NearbyRotor Finsler.RotorHomotopy
open Finsler.H1PuncturedEvaluationChart Finsler.TimedRotorPunctured
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
local notation "I" => _root_.unitInterval

def rotated {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) : C(I, Sphere n) :=
  ⟨fun t => sphereMap (path t (z.val : Ambient n) (a : Ambient n)) (p t), by
    have hf : Continuous (fun t : I => (t, z)) := continuous_id.prodMk continuous_const
    have hA := (operator_continuous a).comp hf
    exact (hA.clm_apply (continuous_subtype_val.comp p.continuous)).subtype_mk _⟩

def unrotated {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) : C(I, Sphere n) :=
  ⟨fun t => sphereMap (path t (z.val : Ambient n) (a : Ambient n)).symm (p t), by
    have hf : Continuous (fun t : I => (t, z)) := continuous_id.prodMk continuous_const
    have hA := (inverse_operator_continuous a).comp hf
    exact (hA.clm_apply (continuous_subtype_val.comp p.continuous)).subtype_mk _⟩

theorem rotated_continuous {n : ℕ} (a : Sphere n) :
    Continuous (fun q : base a × C(I, Sphere n) => rotated a q.1 q.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hf : Continuous (fun q : (base a × C(I, Sphere n)) × I => (q.2, q.1.1)) :=
    continuous_snd.prodMk (continuous_fst.comp continuous_fst)
  have hA := (operator_continuous a).comp hf
  have hv : Continuous (fun q : (base a × C(I, Sphere n)) × I => (q.1.2 q.2 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_eval.comp
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact (hA.clm_apply hv).subtype_mk _

theorem unrotated_continuous {n : ℕ} (a : Sphere n) :
    Continuous (fun q : base a × C(I, Sphere n) => unrotated a q.1 q.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hf : Continuous (fun q : (base a × C(I, Sphere n)) × I => (q.2, q.1.1)) :=
    continuous_snd.prodMk (continuous_fst.comp continuous_fst)
  have hA := (inverse_operator_continuous a).comp hf
  have hv : Continuous (fun q : (base a × C(I, Sphere n)) × I => (q.1.2 q.2 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_eval.comp
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact (hA.clm_apply hv).subtype_mk _

theorem unrotated_rotated {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) :
    unrotated a z (rotated a z p) = p := by
  apply ContinuousMap.ext
  intro t
  exact sphereMap_symm_apply _ _

theorem rotated_unrotated {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) :
    rotated a z (unrotated a z p) = p := by
  apply ContinuousMap.ext
  intro t
  exact sphereMap_apply_symm _ _

theorem rotated_zero {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) :
    rotated a z p 0 = p 0 := by
  apply Subtype.ext
  change path 0 (z.val : Ambient n) (a : Ambient n) (p 0 : Ambient n) = (p 0 : Ambient n)
  rw [path_zero]
  rfl

theorem unrotated_zero {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) :
    unrotated a z p 0 = p 0 := by
  apply Subtype.ext
  change (path 0 (z.val : Ambient n) (a : Ambient n)).symm (p 0 : Ambient n) = (p 0 : Ambient n)
  rw [path_zero]
  rfl

theorem rotated_one {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) (hp : p 1 = z.val) :
    rotated a z p 1 = a := by
  apply Subtype.ext
  change path 1 (z.val : Ambient n) (a : Ambient n) (p 1 : Ambient n) = (a : Ambient n)
  rw [path_one, hp]
  exact rotor_map ((mem_sphere_zero_iff_norm.mp z.val.property).trans
    (mem_sphere_zero_iff_norm.mp a.property).symm)

theorem unrotated_one {n : ℕ} (a : Sphere n) (z : base a) (p : C(I, Sphere n)) (hp : p 1 = a) :
    unrotated a z p 1 = z.val := by
  apply Subtype.ext
  change (path 1 (z.val : Ambient n) (a : Ambient n)).symm (p 1 : Ambient n) = (z.val : Ambient n)
  rw [path_one, hp]
  have he := rotor_map ((mem_sphere_zero_iff_norm.mp z.val.property).trans
    (mem_sphere_zero_iff_norm.mp a.property).symm)
  calc (rotor (z.val : Ambient n) (a : Ambient n)).symm (a : Ambient n) =
      (rotor (z.val : Ambient n) (a : Ambient n)).symm (rotor (z.val : Ambient n) (a : Ambient n) z.val) :=
        congrArg _ he.symm
    _ = (z.val : Ambient n) := LinearIsometryEquiv.symm_apply_apply _ _

end
end Finsler.TimedRotorPathMap
