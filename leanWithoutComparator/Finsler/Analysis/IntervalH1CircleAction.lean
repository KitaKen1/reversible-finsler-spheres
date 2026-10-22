module

public import Finsler.Analysis.IntervalH1Shift

/-! Algebraic rotations of the genuine periodic sphere weak H¹ graph.
Circle phases use the canonical interval representative; faithful actual circle
maps prove the action laws. Joint continuity in strong H¹ is not asserted. 
Strong-H¹ rotation continuity and isometry are proved downstream in
IntervalH1RotationContinuity and IntervalH1RotationIsometry. -/

@[expose] public section

namespace Finsler.SobolevCircleAction

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevShift
open scoped Topology

noncomputable section

def rotateSphere {n : ℕ} (u : SphereLoop n) (a : SobolevCircleRepresentative.Circle) : SphereLoop n :=
  shiftSphere u (circlePoint a)

theorem circleMap_rotateSphere {n : ℕ} (u : SphereLoop n) (a : SobolevCircleRepresentative.Circle) :
    sphereCircleMap (rotateSphere u a) = shiftedSphereMap u a := by
  change sphereCircleMap (shiftSphere u (circlePoint a)) = _
  rw [circleMap_shiftSphere, circlePoint_coe]

theorem rotateSphere_coe {n : ℕ} (u : SphereLoop n) (a : ℝ) :
    rotateSphere u (a : SobolevCircleRepresentative.Circle) = shiftSphere u a := by
  apply sphereCircleMap_injective n
  rw [circleMap_rotateSphere, circleMap_shiftSphere]

theorem rotateSphere_zero {n : ℕ} (u : SphereLoop n) : rotateSphere u 0 = u := by
  apply sphereCircleMap_injective n
  rw [circleMap_rotateSphere, shiftedSphereMap_zero]

theorem rotateSphere_add {n : ℕ} (u : SphereLoop n) (a b : SobolevCircleRepresentative.Circle) :
    rotateSphere (rotateSphere u b) a = rotateSphere u (a + b) := by
  apply sphereCircleMap_injective n
  rw [circleMap_rotateSphere, circleMap_rotateSphere]
  apply ContinuousMap.ext
  intro x
  rw [shiftedSphereMap_apply, circleMap_rotateSphere, shiftedSphereMap_apply,
    shiftedSphereMap_apply]
  congr 1
  ac_rfl

instance (n : ℕ) : AddAction SobolevCircleRepresentative.Circle (SphereLoop n) where
  vadd a u := rotateSphere u a
  zero_vadd := rotateSphere_zero
  add_vadd a b u := (rotateSphere_add u a b).symm

theorem vadd_eq_rotateSphere {n : ℕ} (a : SobolevCircleRepresentative.Circle) (u : SphereLoop n) :
    a +ᵥ u = rotateSphere u a := rfl

theorem sphereCircleMap_vadd {n : ℕ} (a x : SobolevCircleRepresentative.Circle) (u : SphereLoop n) :
    sphereCircleMap (a +ᵥ u) x = sphereCircleMap u (a + x) := by
  change sphereCircleMap (rotateSphere u a) x = _
  rw [circleMap_rotateSphere, shiftedSphereMap_apply]

theorem sphereImage_vadd {n : ℕ} (a : SobolevCircleRepresentative.Circle) (u : SphereLoop n) :
    Finsler.SobolevReverse.sphereImage (a +ᵥ u) = Finsler.SobolevReverse.sphereImage u :=
  sphereImage_shiftSphere u (circlePoint a)

theorem sphereCircleMap_constant {n : ℕ} (x : Sphere n) (a : SobolevCircleRepresentative.Circle) :
    sphereCircleMap (constantSphereLoop x) a = x := by
  rw [sphereCircleMap_point, sphereRepresentative_constantSphereLoop]

theorem constant_vadd {n : ℕ} (a : SobolevCircleRepresentative.Circle) (x : Sphere n) :
    a +ᵥ constantSphereLoop x = constantSphereLoop x := by
  apply sphereCircleMap_injective n
  apply ContinuousMap.ext
  intro t
  rw [sphereCircleMap_vadd, sphereCircleMap_constant, sphereCircleMap_constant]

theorem shiftSphere_add {n : ℕ} (u : SphereLoop n) (a b : ℝ) :
    shiftSphere (shiftSphere u b) a = shiftSphere u (a + b) := by
  rw [← rotateSphere_coe, ← rotateSphere_coe, ← rotateSphere_coe, rotateSphere_add,
    AddCircle.coe_add]

theorem shiftSphere_periodic {n : ℕ} (u : SphereLoop n) :
    Function.Periodic (shiftSphere u) 1 := by
  intro a
  rw [← rotateSphere_coe, ← rotateSphere_coe, AddCircle.coe_add_period]

theorem shiftSphere_neg_cancel {n : ℕ} (u : SphereLoop n) (a : ℝ) :
    shiftSphere (shiftSphere u a) (-a) = u := by
  rw [shiftSphere_add, neg_add_cancel, shiftSphere_zero]

theorem fixed_phase_iff_circleMap {n : ℕ} (u : SphereLoop n) (a : SobolevCircleRepresentative.Circle) :
    a +ᵥ u = u ↔ ∀ x : SobolevCircleRepresentative.Circle,
      sphereCircleMap u (a + x) = sphereCircleMap u x := by
  constructor
  · intro h x
    rw [← sphereCircleMap_vadd, h]
  · intro h
    apply sphereCircleMap_injective n
    apply ContinuousMap.ext
    intro x
    rw [sphereCircleMap_vadd]
    exact h x

end

end Finsler.SobolevCircleAction
