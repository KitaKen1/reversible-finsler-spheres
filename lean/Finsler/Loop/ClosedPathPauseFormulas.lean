module

public import Finsler.Loop.ClosedLoopReparametrization

/-! Exact path/circle formulas for the two pauses occurring in the
ORIGINAL self-cut maps when the two evaluated endpoints coincide. -/
@[expose] public section
namespace Finsler.ClosedPathPauseFormulas
open Finsler.ClosedLoopReparametrization
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem trans_refl {X : Type*} [TopologicalSpace X] {P : X}
    (γ : Path P P) (t : _root_.unitInterval) :
    γ.trans (Path.refl P) t = γ (early.val t) := by
  rw [Path.trans_apply]
  split_ifs with h
  · congr 1
    apply Subtype.ext
    change 2 * (t : ℝ) = min (2 * (t : ℝ)) 1
    exact (min_eq_left (by linarith)).symm
  · have ht : early.val t = 1 := Subtype.ext (min_eq_right (by linarith))
    rw [ht, γ.target]
    rfl

theorem refl_trans {X : Type*} [TopologicalSpace X] {P : X}
    (γ : Path P P) (t : _root_.unitInterval) :
    (Path.refl P).trans γ t = γ (late.val t) := by
  rw [Path.trans_apply]
  split_ifs with h
  · have ht : late.val t = 0 := Subtype.ext (max_eq_right (by linarith))
    rw [ht, γ.source]
    rfl
  · congr 1
    apply Subtype.ext
    change 2 * (t : ℝ) - 1 = max (2 * (t : ℝ) - 1) 0
    exact (max_eq_left (by linarith)).symm

theorem circle_trans_refl {X : Type*} [TopologicalSpace X] {P : X} (γ : Path P P) :
    ClosedPathCircle.circle (ClosedPathCircle.ofPath (γ.trans (Path.refl P))) =
      ClosedPathCircle.circle (warp early (ClosedPathCircle.ofPath γ)) := by
  apply ContinuousMap.ext
  intro a
  rw [ClosedPathCircle.circle_apply, ClosedPathCircle.circle_apply]
  exact trans_refl γ _

theorem circle_refl_trans {X : Type*} [TopologicalSpace X] {P : X} (γ : Path P P) :
    ClosedPathCircle.circle (ClosedPathCircle.ofPath ((Path.refl P).trans γ)) =
      ClosedPathCircle.circle (warp late (ClosedPathCircle.ofPath γ)) := by
  apply ContinuousMap.ext
  intro a
  rw [ClosedPathCircle.circle_apply, ClosedPathCircle.circle_apply]
  exact refl_trans γ _

end
end Finsler.ClosedPathPauseFormulas
