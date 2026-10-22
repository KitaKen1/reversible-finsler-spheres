module

public import Finsler.Loop.NativeSequentialCutParameters

/-! The FIRST tested output of the original prefix branch and the
LAST retained output of the original suffix branch agree LITERALLY
with the common original-loop cuts. All endpoints and seams remain.
These are H1 graph equalities, not just pointwise loop images. -/
@[expose] public section
namespace Finsler.NativeSequentialCutOuterOutputs
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1SelfCutNeighborhood Finsler.NativeSelfCutSegmentClocks
open Finsler.NativeSequentialCutParameters Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {n : ℕ} {r : ℝ}

theorem prefix_endpoint (hr : r ≤ 1) (z : prefixDomain n r) :
    endpoint (prefixInner hr z).val = endpoint (prefixCut hr z).val := left_prefix z.val.1 z.val.2

theorem suffix_endpoint (hr : r ≤ 1) (z : suffixDomain n r) :
    endpoint (suffixInner hr z).val = endpoint (suffixCut hr z).val := right_suffix z.val.1 z.val.2

theorem prefix_point (hr : r ≤ 1) (z : prefixDomain n r) :
    point (prefixInner hr z).val.2 = point (prefixCut hr z).val.2 := point_left z.val.1

theorem suffix_point (hr : r ≤ 1) (z : suffixDomain n r) :
    point (suffixInner hr z).val.2 = point (suffixCut hr z).val.2 := point_right z.val.1

theorem prefix_path (hr : r ≤ 1) (z : prefixDomain n r) :
    prefixPath (prefixInner hr z) = prefixPath (prefixCut hr z) := by
  apply eq_of_representative_eqOn
  intro τ hτ
  change continuousRepresentative (restrict (leftData z.val.1) (by norm_num)
    (firstHalf z.val.2).property (firstHalf z.val.2).property.1) τ = _
  rw [representative_restrict _ _ _ _ hτ]
  have hq := mul_le_of_le_one_right z.val.2.property.1 hτ.2
  have ht : aff 0 (firstHalf z.val.2) τ ∈ Icc (0 : ℝ) (1 / 2) := by
    dsimp [aff, firstHalf]
    constructor <;> nlinarith [mul_nonneg z.val.2.property.1 hτ.1, z.val.2.property.2]
  rw [leftData, representative_concat_left _ _ (by norm_num) (by norm_num) ht]
  have hu := H1ConcatContinuity.left_time_mem (by norm_num : (0 : ℝ) < 1 / 2)
    (aff_mem_Icc (by norm_num) (firstHalf z.val.2).property hτ) ht.2
  rw [prefixPath, representative_restrict _ _ _ _ hu, prefixPath,
    representative_restrict _ _ _ _ hτ]
  congr 1
  change aff 0 (z.val.1.val.1 : ℝ) ((1 / 2 : ℝ)⁻¹ * aff 0 ((z.val.2 : ℝ) / 2) τ) =
    aff 0 ((z.val.1.val.1 : ℝ) * z.val.2) τ
  norm_num [aff]
  ring

theorem suffix_path (hr : r ≤ 1) (z : suffixDomain n r) :
    suffixPath (suffixInner hr z) = suffixPath (suffixCut hr z) := by
  apply eq_of_representative_eqOn
  intro τ hτ
  change continuousRepresentative (restrict (rightData z.val.1)
    (secondHalf z.val.2).property (by norm_num) (secondHalf z.val.2).property.2) τ = _
  rw [representative_restrict _ _ _ _ hτ]
  have ht : aff (secondHalf z.val.2) 1 τ ∈ Icc (1 / 2 : ℝ) 1 := by
    dsimp [aff, secondHalf]
    have hmul := mul_nonneg (sub_nonneg.mpr z.val.2.property.2) hτ.1
    have hle := mul_le_of_le_one_right (sub_nonneg.mpr z.val.2.property.2) hτ.2
    constructor <;> nlinarith [z.val.2.property.1]
  rw [rightData, representative_concat_right _ _ (by norm_num) (by norm_num) (right_match z.val.1) ht]
  have hu := H1ConcatContinuity.right_time_mem (by norm_num : (1 / 2 : ℝ) < 1)
    (aff_mem_Icc (secondHalf z.val.2).property (by norm_num) hτ) ht.1
  rw [suffixPath, representative_restrict _ _ _ _ hu, suffixPath,
    representative_restrict _ _ _ _ hτ]
  congr 1
  change aff (z.val.1.val.1 : ℝ) 1 (rightMap (1 / 2) (aff ((1 + (z.val.2 : ℝ)) / 2) 1 τ)) =
    aff ((z.val.1.val.1 : ℝ) + (1 - z.val.1.val.1) * z.val.2) 1 τ
  norm_num [aff, rightMap]
  ring

theorem prefix_tested (hr : r ≤ 1) (z : prefixDomain n r) :
    left (prefixInner hr z) = left (prefixCut hr z) := by
  apply sphereLoop_data_injective
  change concat (prefixPath (prefixInner hr z))
    (H1ShortArc.arc (endpoint (prefixInner hr z).val) (point (prefixInner hr z).val.2))
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) = _
  rw [prefix_path, prefix_endpoint, prefix_point]
  rfl

theorem suffix_retained (hr : r ≤ 1) (z : suffixDomain n r) :
    right (suffixInner hr z) = right (suffixCut hr z) := by
  apply sphereLoop_data_injective
  change concat (H1ShortArc.arc (point (suffixInner hr z).val.2) (endpoint (suffixInner hr z).val))
    (suffixPath (suffixInner hr z)) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) = _
  rw [suffix_point, suffix_endpoint, suffix_path]
  rfl

theorem prefix_common_first (hr : r ≤ 1) (z : prefixDomain n r) :
    left (prefixInner hr z) = left (NativeOrderedDoubleCutGeometry.firstCut hr (prefixCommon z)) :=
  prefix_tested hr z

theorem prefix_common_last (hr : r ≤ 1) (z : prefixDomain n r) :
    right z.val.1 = right (NativeOrderedDoubleCutGeometry.lastCut hr (prefixCommon z)) := rfl

theorem suffix_common_first (hr : r ≤ 1) (z : suffixDomain n r) :
    left z.val.1 = left (NativeOrderedDoubleCutGeometry.firstCut hr (suffixCommon z)) := rfl

theorem suffix_common_last (hr : r ≤ 1) (z : suffixDomain n r) :
    right (suffixInner hr z) = right (NativeOrderedDoubleCutGeometry.lastCut hr (suffixCommon z)) :=
  suffix_retained hr z

end
end Finsler.NativeSequentialCutOuterOutputs
