module

public import Finsler.Loop.OrthogonalPathOperations
public import Finsler.Loop.OrthogonalSelfCutDistance

/-! Exact orthogonal covariance of the actual H1 two short-arc cuts.
This is a geometric identity and does not assert invariance of a chosen
Thom representative under rotation. -/

@[expose] public section
namespace Finsler.OrthogonalSelfCut

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSpherePath Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase
open Finsler.H1OrthogonalLength Finsler.OrthogonalShortArc Finsler.OrthogonalPathOperations
open Finsler.CompactH1Alignment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {n : ℕ} (A : Ambient n ≃ₗᵢ[ℝ] Ambient n)

def rotatedCut (z : tube n) : tube n :=
  ⟨(z.val.1, rotateLoop A z.val.2), by
    change Finsler.SupportedSelfCut.distance n (z.val.1, rotateLoop A z.val.2) < 1
    rw [OrthogonalSelfCutDistance.distance]
    exact z.property⟩

theorem point_map (u : SphereLoop n) : point (rotateLoop A u) = sphereMap A (point u) := by
  apply Subtype.ext
  exact representative_rotateData A (u.data : Space n) (by norm_num)

theorem endpoint_map (z : tube n) : endpoint (rotatedCut A z).val = sphereMap A (endpoint z.val) := by
  apply Subtype.ext
  exact representative_rotateData A (z.val.2.data : Space n) z.val.1.property

theorem prefix_map (z : tube n) : prefixPath (rotatedCut A z) = rotateData A (prefixPath z) :=
  restrict_map A (z.val.2.data : Space n) (by norm_num) z.val.1.property z.val.1.property.1

theorem suffix_map (z : tube n) : suffixPath (rotatedCut A z) = rotateData A (suffixPath z) :=
  restrict_map A (z.val.2.data : Space n) z.val.1.property (by norm_num) z.val.1.property.2

theorem leftData_map (z : tube n) : leftData (rotatedCut A z) = rotateData A (leftData z) := by
  unfold leftData
  change Finsler.SobolevConcat.concat (prefixPath (rotatedCut A z))
    (H1ShortArc.arc (endpoint (rotatedCut A z).val) (point (rotateLoop A z.val.2))) _ _ = _
  rw [prefix_map, endpoint_map, point_map, arc_map]
  exact concat_map A (prefixPath z) (H1ShortArc.arc (endpoint z.val) (point z.val.2))
    (by norm_num) (by norm_num) (left_match z)

theorem rightData_map (z : tube n) : rightData (rotatedCut A z) = rotateData A (rightData z) := by
  unfold rightData
  change Finsler.SobolevConcat.concat
    (H1ShortArc.arc (point (rotateLoop A z.val.2)) (endpoint (rotatedCut A z).val))
    (suffixPath (rotatedCut A z)) _ _ = _
  rw [point_map, endpoint_map, arc_map, suffix_map]
  exact concat_map A (H1ShortArc.arc (point z.val.2) (endpoint z.val)) (suffixPath z)
    (by norm_num) (by norm_num) (right_match z)

theorem left_map (z : tube n) : left (rotatedCut A z) = rotateLoop A (left z) :=
  sphereLoop_data_injective (leftData_map A z)

theorem right_map (z : tube n) : right (rotatedCut A z) = rotateLoop A (right z) :=
  sphereLoop_data_injective (rightData_map A z)

end
end Finsler.OrthogonalSelfCut
