module

public import Finsler.Loop.NativeSelfCutSegmentClocks

/-! A SECOND original self cut inside the closing-arc half of the
original retained loop. Its actual tested loop is short: its prefix
is a restriction of the original closing arc, plus the new closing
arc. No raw-clock substitution or uniform-tube conclusion is assumed. -/
@[expose] public section
namespace Finsler.NativeClosingArcNestedCut
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
  (NativeSelfCutSegmentClocks.firstHalf z.2, right z.1) ∈ tube n}

def inner (z : domain n) : tube n :=
  ⟨(NativeSelfCutSegmentClocks.firstHalf z.val.2, right z.val.1), z.property⟩

theorem continuous_inner : Continuous (inner (n := n)) := by
  exact ((NativeSelfCutSegmentClocks.continuous_firstHalf.comp
    (continuous_snd.comp continuous_subtype_val)).prodMk
      (continuous_right.comp (continuous_fst.comp continuous_subtype_val))).subtype_mk _

theorem prefix_data (z : domain n) : prefixPath (inner z) =
    restrict (H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val))
      (by norm_num) z.val.2.property z.val.2.property.1 := by
  apply eq_of_representative_eqOn
  intro τ hτ
  change continuousRepresentative (restrict (rightData z.val.1) (by norm_num)
      (NativeSelfCutSegmentClocks.firstHalf z.val.2).property
      (NativeSelfCutSegmentClocks.firstHalf z.val.2).property.1) τ = _
  rw [representative_restrict _ _ _ _ hτ, representative_restrict _ _ _ _ hτ]
  have ht : aff 0 ((NativeSelfCutSegmentClocks.firstHalf z.val.2 : ClosedInterval) : ℝ) τ ∈
      Icc (0 : ℝ) (1 / 2) := by
    dsimp only [NativeSelfCutSegmentClocks.firstHalf, aff]
    have hp := mul_nonneg z.val.2.property.1 hτ.1
    have hq := mul_le_of_le_one_right z.val.2.property.1 hτ.2
    constructor <;> nlinarith [z.val.2.property.2]
  rw [rightData, representative_concat_left _ _ (by norm_num) (by norm_num) ht]
  congr 1
  dsimp only [NativeSelfCutSegmentClocks.firstHalf, aff]
  ring

theorem prefix_length_le (F : ReversibleMetric n) (z : domain n) :
    H1PathLength.length F (prefixPath (inner z)) ≤
      H1PathLength.length F (H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val)) := by
  rw [prefix_data]
  have h := H1PathLength.length_restrictions_add F (H1ShortArc.arc_mem (forward z.val.1)).1 z.val.2
  dsimp only [forward] at h
  have h0 := H1PathLength.length_nonneg F
    (restrict (H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val))
      z.val.2.property (by norm_num) z.val.2.property.2)
  linarith

theorem tested_length_le (F : ReversibleMetric n) (z : domain n) :
    SobolevLength.length F (left (inner z)) ≤
      H1PathLength.length F (H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val)) +
        H1PathLength.length F (H1ShortArc.arc (endpoint (inner z).val) (point (inner z).val.2)) := by
  rw [length_left]
  linarith [prefix_length_le F z]

theorem tested_length_lt (F : ReversibleMetric n) (z : domain n) {ε : ℝ}
    (h₀ : H1PathLength.length F (H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val)) < ε)
    (h₁ : H1PathLength.length F (H1ShortArc.arc (endpoint (inner z).val) (point (inner z).val.2)) < ε) :
    SobolevLength.length F (left (inner z)) < 2 * ε := by
  have h := tested_length_le F z
  linarith

end
end Finsler.NativeClosingArcNestedCut
