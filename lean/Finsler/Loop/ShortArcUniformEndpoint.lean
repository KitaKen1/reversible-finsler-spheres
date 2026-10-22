module

public import Finsler.Loop.NativeSelfCutSegmentClocks

/-! Uniform pointwise endpoint control on the ORIGINAL short arcs,
including both actual closed self-cut arc halves. Constants6 and7
are deliberate coarse bounds, independent of the cut time. -/
@[expose] public section
namespace Finsler.ShortArcUniformEndpoint
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.H1FiberBase Finsler.H1SelfCutNeighborhood Set
open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem velocity_bound (z : H1ShortArc.pairs n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖SphereDistance.segVel (z.val.1 : Ambient n) z.val.2 t‖ ≤
      6 * ‖(z.val.2 : Ambient n) - z.val.1‖ := by
  have hp : ‖(z.val.1 : Ambient n)‖ = 1 := by simp
  have hq : ‖(z.val.2 : Ambient n)‖ = 1 := by simp
  have h := SphereDistance.segVel_sq_le hp hq z.property.le ht
  nlinarith [norm_nonneg (SphereDistance.segVel (z.val.1 : Ambient n) z.val.2 t),
    norm_nonneg ((z.val.2 : Ambient n) - z.val.1)]

theorem distance_start (z : H1ShortArc.pairs n) (t : ClosedInterval) :
    ‖continuousRepresentative (H1ShortArc.arc z.val.1 z.val.2) t - (z.val.1 : Ambient n)‖ ≤
      6 * ‖(z.val.2 : Ambient n) - z.val.1‖ := by
  rw [H1ShortArc.representative_arc _ _ t.property,
    SphereDistance.segCurve_eq_add_integral, SphereDistance.segCurve_zero, add_sub_cancel_left]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (C := 6 * ‖(z.val.2 : Ambient n) - z.val.1‖)
    (f := SphereDistance.segVel (z.val.1 : Ambient n) z.val.2) (fun x hx =>
      velocity_bound z ((uIoc_of_le t.property.1 ▸ hx).1.le |> fun h0 => ⟨h0, ((uIoc_of_le t.property.1 ▸ hx).2).trans t.property.2⟩))
  rw [sub_zero, abs_of_nonneg t.property.1] at h
  exact h.trans (mul_le_of_le_one_right (by positivity) t.property.2)

theorem distance_finish (z : H1ShortArc.pairs n) (t : ClosedInterval) :
    ‖continuousRepresentative (H1ShortArc.arc z.val.1 z.val.2) t - (z.val.2 : Ambient n)‖ ≤
      7 * ‖(z.val.2 : Ambient n) - z.val.1‖ := by
  have h := distance_start z t
  have ht := norm_sub_le_norm_sub_add_norm_sub (continuousRepresentative (H1ShortArc.arc z.val.1 z.val.2) t)
    (z.val.1 : Ambient n) (z.val.2 : Ambient n)
  rw [norm_sub_rev (z.val.1 : Ambient n) (z.val.2 : Ambient n)] at ht
  linarith

theorem right_arc_distance (z : tube n) (u : ClosedInterval) :
    ‖(endpoint (NativeSelfCutSegmentClocks.firstHalf u, right z) : Ambient n) - point (right z)‖ ≤
      6 * ‖(endpoint z.val : Ambient n) - point z.val.2‖ := by
  change ‖(sphereRepresentative (right z) (NativeSelfCutSegmentClocks.firstHalf u) : Ambient n) -
    (point (right z) : Ambient n)‖ ≤ _
  have hp : point (right z) = point z.val.2 := by
    apply Subtype.ext
    exact basepoint_right z
  rw [hp, NativeSelfCutSegmentClocks.right_closing_arc]
  exact distance_start (forward z) u

theorem left_arc_distance (z : tube n) (u : ClosedInterval) :
    ‖(endpoint (NativeSelfCutSegmentClocks.secondHalf u, left z) : Ambient n) - point (left z)‖ ≤
      7 * ‖(endpoint z.val : Ambient n) - point z.val.2‖ := by
  change ‖(sphereRepresentative (left z) (NativeSelfCutSegmentClocks.secondHalf u) : Ambient n) -
    (point (left z) : Ambient n)‖ ≤ _
  have hp : point (left z) = point z.val.2 := by
    apply Subtype.ext
    exact basepoint_left z
  rw [hp, NativeSelfCutSegmentClocks.left_closing_arc]
  have h := distance_finish (backward z) u
  simpa only [backward, norm_sub_rev] using h

end
end Finsler.ShortArcUniformEndpoint
