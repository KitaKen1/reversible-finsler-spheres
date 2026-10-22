module

public import Finsler.Topology.JoinSplitHomotopy

/-! Actual positive binary splits realizing the three retained durations
in the first half of a joined loop. The excluded endpoint t=1 is handled
by a separate collar argument. -/

@[expose] public section
namespace Finsler.FirstHalfSplits

open Finsler.VariableJoinContinuity Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def Times : Set ℝ := Ico 0 1

def inner (t : Times) : Splits :=
  ⟨(2 - (t : ℝ)) / (3 - 2 * (t : ℝ)), by
    have hn : 0 < 2 - (t : ℝ) := by linarith [t.property.2]
    have hd : 0 < 3 - 2 * (t : ℝ) := by linarith [t.property.2]
    exact ⟨div_pos hn hd, (div_lt_one hd).mpr (by linarith [t.property.2])⟩⟩

def outer (t : Times) : Splits :=
  ⟨(3 - 2 * (t : ℝ)) / (2 * (2 - (t : ℝ))), by
    have hn : 0 < 3 - 2 * (t : ℝ) := by linarith [t.property.2]
    have hd : 0 < 2 * (2 - (t : ℝ)) := by linarith [t.property.2]
    exact ⟨div_pos hn hd, (div_lt_one hd).mpr (by linarith)⟩⟩

theorem continuous_inner : Continuous inner :=
  (((continuous_const.sub continuous_subtype_val).div
    (continuous_const.sub (continuous_const.mul continuous_subtype_val))
    (fun t => by have h := t.property.2; dsimp; linarith)).subtype_mk _)

theorem continuous_outer : Continuous outer :=
  (((continuous_const.sub (continuous_const.mul continuous_subtype_val)).div
    (continuous_const.mul (continuous_const.sub continuous_subtype_val))
    (fun t => by have h := t.property.2; dsimp; nlinarith)).subtype_mk _)

theorem first_duration (t : Times) : (outer t : ℝ) * inner t = 1 / 2 := by
  have h₂ : 2 - (t : ℝ) ≠ 0 := by linarith [t.property.2]
  have h₃ : 3 - 2 * (t : ℝ) ≠ 0 := by linarith [t.property.2]
  change ((3 - 2 * (t : ℝ)) / (2 * (2 - (t : ℝ)))) *
    ((2 - (t : ℝ)) / (3 - 2 * (t : ℝ))) = 1 / 2
  field_simp
  <;> ring

theorem second_duration (t : Times) :
    (outer t : ℝ) * (1 - (inner t : ℝ)) = (1 - (t : ℝ)) / (2 * (2 - (t : ℝ))) := by
  have h₂ : 2 - (t : ℝ) ≠ 0 := by linarith [t.property.2]
  have h₃ : 3 - 2 * (t : ℝ) ≠ 0 := by linarith [t.property.2]
  change ((3 - 2 * (t : ℝ)) / (2 * (2 - (t : ℝ)))) *
    (1 - ((2 - (t : ℝ)) / (3 - 2 * (t : ℝ)))) = _
  field_simp
  <;> ring

theorem third_duration (t : Times) : 1 - (outer t : ℝ) = 1 / (2 * (2 - (t : ℝ))) := by
  have h₂ : 2 - (t : ℝ) ≠ 0 := by linarith [t.property.2]
  change 1 - ((3 - 2 * (t : ℝ)) / (2 * (2 - (t : ℝ)))) = _
  field_simp
  <;> ring

def splits (z : _root_.unitInterval × Times) : Splits × Splits :=
  (JoinSplitHomotopy.interpolate (inner z.2) JoinSplitHomotopy.half z.1,
    JoinSplitHomotopy.interpolate (outer z.2) JoinSplitHomotopy.half z.1)

theorem continuous_splits : Continuous splits := by
  have hs : Continuous (fun z : _root_.unitInterval × Times => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hi : Continuous (fun z : _root_.unitInterval × Times => (inner z.2 : ℝ)) :=
    (continuous_subtype_val.comp continuous_inner).comp continuous_snd
  have ho : Continuous (fun z : _root_.unitInterval × Times => (outer z.2 : ℝ)) :=
    (continuous_subtype_val.comp continuous_outer).comp continuous_snd
  exact ((((continuous_const.sub hs).mul hi).add (hs.mul continuous_const)).subtype_mk _).prodMk
    ((((continuous_const.sub hs).mul ho).add (hs.mul continuous_const)).subtype_mk _)

theorem splits_zero (t : Times) : splits (0, t) = (inner t, outer t) := by
  simp only [splits, JoinSplitHomotopy.interpolate_zero]

theorem splits_one (t : Times) : splits (1, t) = (JoinSplitHomotopy.half, JoinSplitHomotopy.half) := by
  simp only [splits, JoinSplitHomotopy.interpolate_one]

end
end Finsler.FirstHalfSplits
