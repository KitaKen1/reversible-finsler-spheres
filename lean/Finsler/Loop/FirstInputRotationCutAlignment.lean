module

public import Finsler.Loop.OrthogonalSelfCut
public import Finsler.Loop.FirstInputRotatingFixedOutput

/-! Identify the corrected retained endpoint with alignment of the
original retained cut. Exact short-arc covariance supplies the missing
geometric endpoint, independently of any Thom-cochain invariance. -/

@[expose] public section
namespace Finsler.FirstInputRotationCutAlignment

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.H1OrthogonalLength
open Finsler.H1AlignmentHomotopy Finsler.CompactH1Alignment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1)

theorem rotated_cut (s : _root_.unitInterval) (z : FirstInputRotatingCut.source α β R r) :
    OrthogonalSelfCut.rotatedCut
      (RotorHomotopy.path s (basepoint (α z.val.2.val.1)) (point (β z.val.2.val.2)))
      (FirstInputRotatingCut.original α β R r hR hr z) =
        FirstInputRotatingCut.rotation α β R r hR hr (s, z) := by
  apply Subtype.ext
  change ((FirstInputRotatingCut.original α β R r hR hr z).val.1,
    rotateLoop (RotorHomotopy.path s (basepoint (α z.val.2.val.1)) (point (β z.val.2.val.2)))
      (FirstInputRotatingCut.original α β R r hR hr z).val.2) = _
  rw [FirstInputRotatingCut.original_parameters,
    FirstInputRotatingCut.rotation_parameters α β R r hR hr (hR.trans_lt (by norm_num))]
  rfl

theorem right_hom (s : _root_.unitInterval) (z : FirstInputRotatingCut.source α β R r) :
    right (FirstInputRotatingCut.rotation α β R r hR hr (s, z)) =
      hom s (right (FirstInputRotatingCut.original α β R r hR hr z)) (point (β z.val.2.val.2)) := by
  rw [← rotated_cut α β R r hR hr s z, OrthogonalSelfCut.right_map]
  unfold hom
  rw [basepoint_right]
  rfl

theorem left_hom (s : _root_.unitInterval) (z : FirstInputRotatingCut.source α β R r) :
    left (FirstInputRotatingCut.rotation α β R r hR hr (s, z)) =
      hom s (left (FirstInputRotatingCut.original α β R r hR hr z)) (point (β z.val.2.val.2)) := by
  rw [← rotated_cut α β R r hR hr s z, OrthogonalSelfCut.left_map]
  unfold hom
  rw [basepoint_left]
  rfl

theorem right_one (z : FirstInputRotatingCut.source α β R r) :
    right (FirstInputRotatingCut.rotation α β R r hR hr (1, z)) =
      align (right (FirstInputRotatingCut.original α β R r hR hr z)) (point (β z.val.2.val.2)) := by
  rw [right_hom, hom_one]

theorem left_one (z : FirstInputRotatingCut.source α β R r) :
    left (FirstInputRotatingCut.rotation α β R r hR hr (1, z)) =
      align (left (FirstInputRotatingCut.original α β R r hR hr z)) (point (β z.val.2.val.2)) := by
  rw [left_hom, hom_one]

def originalRetainedPair (z : FirstInputRotatingCut.source α β R r) : H1JoinContinuity.composable n :=
  ⟨(align (right (FirstInputRotatingCut.original α β R r hR hr z)) (point (β z.val.2.val.2)),
    β z.val.2.val.2), basepoint_align _ _⟩

theorem retained_pair_eq (z : FirstInputRotatingCut.source α β R r) :
    originalRetainedPair α β R r hR hr z = FirstInputRotatingFixedOutput.endPair α β R r hR hr z := by
  apply Subtype.ext
  exact Prod.ext (right_one α β R r hR hr z).symm rfl

theorem output_eq_original_join (z : FirstInputRotatingCut.source α β R r) :
    FirstInputRotatingFixedOutput.output α β R r hR hr z =
      H1JoinContinuity.joinMap (1 / 2) (by norm_num) (by norm_num)
        (originalRetainedPair α β R r hR hr z) := by
  rw [retained_pair_eq]
  rfl

end
end Finsler.FirstInputRotationCutAlignment
