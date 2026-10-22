module

public import Finsler.Geometry.RotorInverse
public import Finsler.Analysis.H1AlignmentHomotopy

/-! A genuine local product chart for evaluation at the basepoint.
All spaces carry the original strong H¹ or sphere topology. -/

@[expose] public section

namespace Finsler.H1FiberBase

open Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy
open Finsler.H1OrthogonalLength Finsler.H1OrthogonalContinuity
open Finsler.NearbyRotor Finsler.RotorInverse
open Set
open scoped Topology

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

def point (u : SphereLoop n) : Sphere n :=
  sphereRepresentative u ⟨0, by norm_num⟩

theorem continuous_point : Continuous (point : SphereLoop n → Sphere n) :=
  basepoint_continuous.subtype_mk _

theorem basepoint_align (u : SphereLoop n) (y : Sphere n) :
    basepoint (align u y) = (y : Ambient n) := by
  simpa only [hom_one] using hom_end_basepoint u y

theorem rotateLoop_inverse (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : SphereLoop n) :
    rotateLoop A.symm (rotateLoop A u) = u := by
  calc
    _ = rotateLoop (A.trans A.symm) u := rotateLoop_comp A.symm A u
    _ = u := by rw [LinearIsometryEquiv.self_trans_symm]; exact rotateLoop_refl u

theorem align_reverse (u : SphereLoop n) (y : Sphere n) :
    align (align u y) (point u) = u := by
  have hy : ‖(y : Ambient n)‖ = 1 := by simpa using y.property
  have he := rotor_symm ((u.sphere_constraint ⟨0, by norm_num⟩).trans hy.symm)
  have hA : rotor (basepoint (align u y)) (basepoint u) =
      (rotor (basepoint u) (y : Ambient n)).symm := by
    rw [basepoint_align]
    exact he.symm
  have hc := congrArg (fun A : Ambient n ≃ₗᵢ[ℝ] Ambient n => rotateLoop A (align u y)) hA
  exact hc.trans (rotateLoop_inverse (rotor (basepoint u) (y : Ambient n)) u)


end
end Finsler.H1FiberBase
