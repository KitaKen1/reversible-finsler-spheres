module

public import Finsler.Loop.NativeBVRotationSquare
public import Finsler.Loop.WholeSelfCutComplement

/-! Remove the time-dependent rotation of the ORIGINAL complemented
cut square by a genuine joint-continuous H1 homotopy. Its cut faces
stay diagonal and its two periodic rotation faces agree throughout. -/
@[expose] public section
namespace Finsler.ComplementRotationShear
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.SobolevRotation
open Finsler.NativeBVRotationSquare Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def reflected (n : ℕ) : squareDomain n ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (unitInterval.symm z.1, rotationMap n z.2), by
    have ht : Continuous (fun z : squareDomain n => unitInterval.symm z.1) := by fun_prop
    exact ht.prodMk ((rotationMap n).hom.continuous.comp continuous_snd)⟩

theorem complement_value (n : ℕ) (z : squareDomain n) :
    (intoCut n ≫ WholeSelfCutComplement.complement n) z =
      (unitInterval.symm z.1, shiftSphere z.2.2 ((z.2.1 : ℝ) + (z.1 : ℝ))) := by
  change (_, shiftSphere (shiftSphere z.2.2 (z.2.1 : ℝ)) (z.1 : ℝ)) = _
  rw [shiftSphere_add, add_comm (z.1 : ℝ)]
  rfl

private theorem family_continuous (n : ℕ) :
    Continuous (fun z : _root_.unitInterval × squareDomain n =>
      (unitInterval.symm z.2.1,
        shiftSphere z.2.2.2 ((z.2.2.1 : ℝ) + (z.1 : ℝ) * (z.2.1 : ℝ)))) := by
  have hp : Continuous (fun z : _root_.unitInterval × squareDomain n =>
      (z.2.2.2, (z.2.2.1 : ℝ) + (z.1 : ℝ) * (z.2.1 : ℝ))) := by fun_prop
  have ht : Continuous (fun z : _root_.unitInterval × squareDomain n => unitInterval.symm z.2.1) := by fun_prop
  exact ht.prodMk (((shiftSphere_joint_continuous n).comp hp).congr (fun _ => rfl))

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
def homotopy (n : ℕ) : TopCat.Homotopy (reflected n)
    (intoCut n ≫ WholeSelfCutComplement.complement n) where
  toFun z := (unitInterval.symm z.2.1,
    shiftSphere z.2.2.2 ((z.2.2.1 : ℝ) + (z.1 : ℝ) * (z.2.1 : ℝ)))
  continuous_toFun := by
    exact family_continuous n
  map_zero_left z := by
    change (_, shiftSphere z.2.2 ((z.2.1 : ℝ) + 0 * (z.1 : ℝ))) = _
    simp only [zero_mul, add_zero]
    rfl
  map_one_left z := by
    change (_, shiftSphere z.2.2 ((z.2.1 : ℝ) + 1 * (z.1 : ℝ))) = _
    rw [one_mul, complement_value]

theorem cut_face_diagonal (n : ℕ) (t : _root_.unitInterval) (ht : t = 0 ∨ t = 1)
    (v : _root_.unitInterval) (z : rotationDomain n) :
    homotopy n (v, (t, z)) ∈ FilteredGlobalThomTime.endpointCarrier n := by
  rcases ht with rfl | rfl
  · change H1FiberBase.point _ = H1SelfCutNeighborhood.endpoint _
    change sphereRepresentative _ 0 = sphereRepresentative _ (unitInterval.symm 0)
    rw [unitInterval.symm_zero]
    exact (sphereRepresentative_endpoints _).symm
  · change H1FiberBase.point _ = H1SelfCutNeighborhood.endpoint _
    change sphereRepresentative _ 0 = sphereRepresentative _ (unitInterval.symm 1)
    rw [unitInterval.symm_one]

theorem rotation_faces (n : ℕ) (v : _root_.unitInterval) (z : parameters n) :
    homotopy n (v, rotationFace n 0 z) = homotopy n (v, rotationFace n 1 z) := by
  change (unitInterval.symm z.1, shiftSphere z.2 (0 + (v : ℝ) * (z.1 : ℝ))) =
    (unitInterval.symm z.1, shiftSphere z.2 (1 + (v : ℝ) * (z.1 : ℝ)))
  apply Prod.ext
  · rfl
  change shiftSphere z.2 (0 + (v : ℝ) * (z.1 : ℝ)) =
    shiftSphere z.2 (1 + (v : ℝ) * (z.1 : ℝ))
  rw [zero_add, add_comm 1]
  exact (shiftSphere_periodic z.2 _).symm

theorem rotation_homotopies (n : ℕ) :
    ((homotopy n).comp (TopCat.Homotopy.refl (rotationFace n 0))).h =
      ((homotopy n).comp (TopCat.Homotopy.refl (rotationFace n 1))).h := by
  ext z : 1
  exact rotation_faces n z.2.down z.1

end
end Finsler.ComplementRotationShear
