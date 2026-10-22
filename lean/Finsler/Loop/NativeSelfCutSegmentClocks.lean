module

public import Finsler.Analysis.H1SelfCutNeighborhood

/-! Exact clocks for the ORIGINAL H1 self cuts, including both closing
arc halves. The raw prefix/suffix occupy only half the closed loop.
All four formulas include their endpoints and the seam. -/
@[expose] public section
namespace Finsler.NativeSelfCutSegmentClocks
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1SelfCutNeighborhood Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
variable {n : ℕ}

def firstHalf (u : ClosedInterval) : ClosedInterval :=
  ⟨(u : ℝ) / 2, by constructor <;> linarith [u.property.1, u.property.2]⟩

def secondHalf (u : ClosedInterval) : ClosedInterval :=
  ⟨(1 + (u : ℝ)) / 2, by constructor <;> linarith [u.property.1, u.property.2]⟩

def prefixTime (t u : ClosedInterval) : ClosedInterval :=
  ⟨(t : ℝ) * u, mul_nonneg t.property.1 u.property.1,
    (mul_le_of_le_one_right t.property.1 u.property.2).trans t.property.2⟩

def suffixTime (t u : ClosedInterval) : ClosedInterval :=
  ⟨(t : ℝ) + (1 - t) * u, by
    have ht := sub_nonneg.mpr t.property.2
    constructor
    · exact add_nonneg t.property.1 (mul_nonneg ht u.property.1)
    · have hu := mul_le_of_le_one_right ht u.property.2
      linarith⟩

theorem continuous_firstHalf : Continuous firstHalf := by unfold firstHalf; fun_prop
theorem continuous_secondHalf : Continuous secondHalf := by unfold secondHalf; fun_prop
theorem continuous_prefixTime : Continuous (fun z : ClosedInterval × ClosedInterval => prefixTime z.1 z.2) := by
  unfold prefixTime; fun_prop
theorem continuous_suffixTime : Continuous (fun z : ClosedInterval × ClosedInterval => suffixTime z.1 z.2) := by
  unfold suffixTime; fun_prop

theorem left_prefix (z : tube n) (u : ClosedInterval) :
    sphereRepresentative (left z) (firstHalf u) =
      sphereRepresentative z.val.2 (prefixTime z.val.1 u) := by
  apply Subtype.ext
  change continuousRepresentative (leftData z) ((u : ℝ) / 2) = _
  rw [leftData, representative_concat_left _ _ (by norm_num) (by norm_num)
    (by constructor <;> linarith [u.property.1, u.property.2])]
  have ht : (1 / 2 : ℝ)⁻¹ * ((u : ℝ) / 2) = (u : ℝ) := by ring
  rw [ht]
  rw [prefixPath, representative_restrict _ _ _ _ u.property]
  congr 1
  simp only [aff, prefixTime]
  ring

theorem left_closing_arc (z : tube n) (u : ClosedInterval) :
    (sphereRepresentative (left z) (secondHalf u) : Ambient n) =
      continuousRepresentative (H1ShortArc.arc (endpoint z.val) (point z.val.2)) u := by
  change continuousRepresentative (leftData z) ((1 + (u : ℝ)) / 2) = _
  rw [leftData, representative_concat_right _ _ (by norm_num) (by norm_num) (left_match z)
    (by constructor <;> linarith [u.property.1, u.property.2])]
  congr 1
  norm_num [rightMap]
  ring

theorem right_closing_arc (z : tube n) (u : ClosedInterval) :
    (sphereRepresentative (right z) (firstHalf u) : Ambient n) =
      continuousRepresentative (H1ShortArc.arc (point z.val.2) (endpoint z.val)) u := by
  change continuousRepresentative (rightData z) ((u : ℝ) / 2) = _
  rw [rightData, representative_concat_left _ _ (by norm_num) (by norm_num)
    (by constructor <;> linarith [u.property.1, u.property.2])]
  congr 1
  ring

theorem right_suffix (z : tube n) (u : ClosedInterval) :
    sphereRepresentative (right z) (secondHalf u) =
      sphereRepresentative z.val.2 (suffixTime z.val.1 u) := by
  apply Subtype.ext
  change continuousRepresentative (rightData z) ((1 + (u : ℝ)) / 2) = _
  rw [rightData, representative_concat_right _ _ (by norm_num) (by norm_num) (right_match z)
    (by constructor <;> linarith [u.property.1, u.property.2])]
  have ht : rightMap (1 / 2) ((1 + (u : ℝ)) / 2) = (u : ℝ) := by
    norm_num [rightMap]
    ring
  rw [ht, suffixPath, representative_restrict _ _ _ _ u.property]
  congr 1

end
end Finsler.NativeSelfCutSegmentClocks
