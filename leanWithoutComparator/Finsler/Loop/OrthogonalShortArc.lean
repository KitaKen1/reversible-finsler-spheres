module

public import Finsler.Analysis.H1ShortArc
public import Finsler.Analysis.H1OrthogonalLength

/-! The actual rational stereographic closing arc commutes with every
ambient orthogonal map, including its original H1 parametrization. -/

@[expose] public section
namespace Finsler.OrthogonalShortArc

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.RationalSphereCurve Finsler.SobolevSphereChart Finsler.SobolevSpherePath
open Finsler.H1OrthogonalLength
open Set
open scoped RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 500000

variable {n : ℕ} (A : Ambient n ≃ₗᵢ[ℝ] Ambient n)

def sphereMap (P : Sphere n) : Sphere n :=
  ⟨A (P : Ambient n), by
    have hp : ‖(P : Ambient n)‖ = 1 := by simpa using P.property
    simpa using (A.norm_map (P : Ambient n)).trans hp⟩

theorem stereo_map (p q : Ambient n) :
    stereo (A p) (A q) = A (stereo p q) := by
  simp only [stereo, A.inner_map_map, map_smul, map_sub]

theorem ratMap_map (r : ℝ) (p q : Ambient n) :
    ratMap r (A p, A q) = A (ratMap r (p, q)) := by
  simp only [ratMap, aFun, A.norm_map, map_smul, map_add]

theorem segCurve_map (p q : Ambient n) (t : ℝ) :
    SphereDistance.segCurve (A p) (A q) t = A (SphereDistance.segCurve p q t) := by
  unfold SphereDistance.segCurve
  rw [stereo_map, ← A.map_smul]
  exact ratMap_map A 1 p (t • stereo p q)

theorem arc_map (P Q : Sphere n) :
    H1ShortArc.arc (sphereMap A P) (sphereMap A Q) = rotateData A (H1ShortArc.arc P Q) := by
  apply eq_of_representative_eqOn
  intro t ht
  rw [H1ShortArc.representative_arc _ _ ht, representative_rotateData _ _ ht,
    H1ShortArc.representative_arc _ _ ht]
  exact segCurve_map A P Q t

end
end Finsler.OrthogonalShortArc
