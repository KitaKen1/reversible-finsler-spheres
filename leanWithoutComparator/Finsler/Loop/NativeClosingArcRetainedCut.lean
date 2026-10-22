module

public import Finsler.Loop.NativeSelfCutSegmentClocks

/-! The other ORIGINAL closing-arc branch: cut the original tested
loop in its closing-arc half. The ACTUAL retained loop consists of
the new short arc and a restriction of the original closing arc. -/
@[expose] public section
namespace Finsler.NativeClosingArcRetainedCut
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1SelfCutNeighborhood Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
variable {n : ℕ}

abbrev domain (n : ℕ) := {z : tube n × ClosedInterval |
  (NativeSelfCutSegmentClocks.secondHalf z.2, left z.1) ∈ tube n}

def inner (z : domain n) : tube n :=
  ⟨(NativeSelfCutSegmentClocks.secondHalf z.val.2, left z.val.1), z.property⟩

theorem continuous_inner : Continuous (inner (n := n)) := by
  exact ((NativeSelfCutSegmentClocks.continuous_secondHalf.comp
    (continuous_snd.comp continuous_subtype_val)).prodMk
      (continuous_left.comp (continuous_fst.comp continuous_subtype_val))).subtype_mk _

theorem suffix_data (z : domain n) : suffixPath (inner z) =
    restrict (H1ShortArc.arc (endpoint z.val.1.val) (point z.val.1.val.2))
      z.val.2.property (by norm_num) z.val.2.property.2 := by
  apply eq_of_representative_eqOn
  intro τ hτ
  change continuousRepresentative (restrict (leftData z.val.1)
      (NativeSelfCutSegmentClocks.secondHalf z.val.2).property (by norm_num)
      (NativeSelfCutSegmentClocks.secondHalf z.val.2).property.2) τ = _
  rw [representative_restrict _ _ _ _ hτ, representative_restrict _ _ _ _ hτ]
  have ht : aff ((NativeSelfCutSegmentClocks.secondHalf z.val.2 : ClosedInterval) : ℝ) 1 τ ∈
      Icc (1 / 2 : ℝ) 1 := by
    dsimp only [NativeSelfCutSegmentClocks.secondHalf, aff]
    have hp := mul_nonneg (sub_nonneg.mpr z.val.2.property.2) hτ.1
    have hq := mul_le_of_le_one_right (sub_nonneg.mpr z.val.2.property.2) hτ.2
    constructor <;> nlinarith [z.val.2.property.1]
  rw [leftData, representative_concat_right _ _ (by norm_num) (by norm_num) (left_match z.val.1) ht]
  congr 1
  norm_num [NativeSelfCutSegmentClocks.secondHalf, aff, rightMap]
  ring

theorem suffix_length_le (F : ReversibleMetric n) (z : domain n) :
    H1PathLength.length F (suffixPath (inner z)) ≤
      H1PathLength.length F (H1ShortArc.arc (endpoint z.val.1.val) (point z.val.1.val.2)) := by
  rw [suffix_data]
  have h := H1PathLength.length_restrictions_add F (H1ShortArc.arc_mem (backward z.val.1)).1 z.val.2
  dsimp only [backward] at h
  have h0 := H1PathLength.length_nonneg F
    (restrict (H1ShortArc.arc (endpoint z.val.1.val) (point z.val.1.val.2))
      (by norm_num) z.val.2.property z.val.2.property.1)
  linarith

theorem retained_length_le (F : ReversibleMetric n) (z : domain n) :
    SobolevLength.length F (right (inner z)) ≤
      H1PathLength.length F (H1ShortArc.arc (point (inner z).val.2) (endpoint (inner z).val)) +
        H1PathLength.length F (H1ShortArc.arc (endpoint z.val.1.val) (point z.val.1.val.2)) := by
  rw [length_right]
  linarith [suffix_length_le F z]

theorem retained_length_lt (F : ReversibleMetric n) (z : domain n) {ε : ℝ}
    (h₀ : H1PathLength.length F (H1ShortArc.arc (point (inner z).val.2) (endpoint (inner z).val)) < ε)
    (h₁ : H1PathLength.length F (H1ShortArc.arc (endpoint z.val.1.val) (point z.val.1.val.2)) < ε) :
    SobolevLength.length F (right (inner z)) < 2 * ε := by
  have h := retained_length_le F z
  linarith

end
end Finsler.NativeClosingArcRetainedCut
