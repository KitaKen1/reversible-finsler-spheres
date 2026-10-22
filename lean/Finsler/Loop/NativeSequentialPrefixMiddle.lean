module

public import Finsler.Loop.NativeSequentialCutOuterOutputs
public import Finsler.Loop.NativeMiddleSplitHomotopy
public import Finsler.Topology.HalfConcatRestriction

/-! The ORIGINAL retained middle loop of the prefix branch is exactly
the common three paths with its actual tail split. On u<1, a genuine
strong-H1 homotopy moves that split to the common half timing, with
EXACT length preservation and fixed basepoint. The excluded u=1
closing-arc seam is a separate relative-support obligation. -/
@[expose] public section
namespace Finsler.NativeSequentialPrefixMiddle
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1SelfCutNeighborhood Finsler.NativeSelfCutSegmentClocks
open Finsler.NativeSequentialCutParameters Finsler.NativeSequentialCutOuterOutputs
open Finsler.VariableJoinContinuity Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {n : ℕ} {r : ℝ}

abbrev inputs (n : ℕ) (r : ℝ) := {z : prefixDomain n r | (z.val.2 : ℝ) < 1}

def time (z : inputs n r) : FirstHalfSplits.Times :=
  ⟨z.val.val.2, z.val.val.2.property.1, z.property⟩

theorem continuous_time : Continuous (time (n := n) (r := r)) := by
  unfold time
  fun_prop

theorem middle_restriction (z : inputs n r) :
    restrict (prefixPath z.val.val.1) z.val.val.2.property (by norm_num) z.val.val.2.property.2 =
      NativeOrderedDoubleCutGeometry.rawMiddle (prefixCommon z.val) := by
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_restrict _ _ _ _ hτ, prefixPath,
    representative_restrict _ _ _ _ (aff_mem_Icc z.val.val.2.property (by norm_num) hτ),
    NativeOrderedDoubleCutGeometry.rawMiddle, representative_restrict _ _ _ _ hτ]
  congr 1
  change aff 0 (z.val.val.1.val.1 : ℝ) (aff (z.val.val.2 : ℝ) 1 τ) =
    aff ((z.val.val.1.val.1 : ℝ) * z.val.val.2) z.val.val.1.val.1 τ
  dsimp [aff]
  ring

theorem suffix_data (hr : r ≤ 1) (z : inputs n r) : suffixPath (prefixInner hr z.val) =
    concat (NativeOrderedDoubleCutGeometry.rawMiddle (prefixCommon z.val))
      (NativeOrderedDoubleCutGeometry.lastArc hr (prefixCommon z.val))
      (HalfConcatRestriction.tailSplit (time z)).property.1
      (HalfConcatRestriction.tailSplit (time z)).property.2 := by
  have h := HalfConcatRestriction.suffix (prefixPath z.val.val.1)
    (H1ShortArc.arc (endpoint z.val.val.1.val) (point z.val.val.1.val.2)) (time z) (left_match z.val.val.1)
  change suffixPath (prefixInner hr z.val) =
    concat (restrict (prefixPath z.val.val.1) z.val.val.2.property (by norm_num) z.val.val.2.property.2)
      (NativeOrderedDoubleCutGeometry.lastArc hr (prefixCommon z.val))
      (HalfConcatRestriction.tailSplit (time z)).property.1
      (HalfConcatRestriction.tailSplit (time z)).property.2 at h
  exact h.trans (congrArg (fun w : Space n => concat w
    (NativeOrderedDoubleCutGeometry.lastArc hr (prefixCommon z.val))
    (HalfConcatRestriction.tailSplit (time z)).property.1
    (HalfConcatRestriction.tailSplit (time z)).property.2) (middle_restriction z))

def splitInput (z : inputs n r) : NativeMiddleSplitHomotopy.inputs n r :=
  (HalfConcatRestriction.tailSplit (time z), prefixCommon z.val)

theorem continuous_splitInput : Continuous (splitInput (n := n) (r := r)) := by
  have ht : Continuous (fun z : inputs n r => HalfConcatRestriction.tailSplit (time z)) := by
    apply Continuous.subtype_mk
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_time)).div
      (continuous_const.sub (continuous_subtype_val.comp continuous_time))
      (fun z => by
        have hu : (z.val.val.2 : ℝ) < 1 := z.property
        change 2 - (z.val.val.2 : ℝ) ≠ 0
        linarith)
  exact ht.prodMk (continuous_prefixCommon.comp continuous_subtype_val)

theorem original_eq (hr : r ≤ 1) (z : inputs n r) :
    right (prefixInner hr z.val) = NativeMiddleSplitHomotopy.loop hr (splitInput z) := by
  apply sphereLoop_data_injective
  change concat (H1ShortArc.arc (point (prefixInner hr z.val).val.2) (endpoint (prefixInner hr z.val).val))
    (suffixPath (prefixInner hr z.val)) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) = _
  rw [prefix_point, prefix_endpoint, suffix_data]
  rfl

def originalMap (hr : r ≤ 1) : C(inputs n r, SphereLoop n) :=
  ⟨fun z => right (prefixInner hr z.val),
    (continuous_right (n := n)).comp ((continuous_prefixInner hr).comp continuous_subtype_val)⟩

def commonMap (hr : r ≤ 1) : C(inputs n r, SphereLoop n) :=
  ⟨fun z => NativeOrderedDoubleCutGeometry.middle hr (prefixCommon z.val),
    (NativeOrderedDoubleCutGeometry.continuous_middle hr).comp
      (continuous_prefixCommon.comp continuous_subtype_val)⟩

def homotopy (hr : r ≤ 1) : (originalMap (n := n) (r := r) hr).Homotopy (commonMap hr) where
  toFun z := NativeMiddleSplitHomotopy.homotopy hr (z.1, splitInput z.2)
  continuous_toFun := (NativeMiddleSplitHomotopy.homotopy hr).continuous.comp
    (continuous_fst.prodMk (continuous_splitInput.comp continuous_snd))
  map_zero_left z := (NativeMiddleSplitHomotopy.homotopy hr).map_zero_left (splitInput z) |>.trans (original_eq hr z).symm
  map_one_left z := (NativeMiddleSplitHomotopy.homotopy hr).map_one_left (splitInput z)

theorem homotopy_length (hr : r ≤ 1) (F : ReversibleMetric n)
    (s : _root_.unitInterval) (z : inputs n r) :
    SobolevLength.length F (homotopy hr (s, z)) =
      SobolevLength.length F (NativeOrderedDoubleCutGeometry.middle hr (prefixCommon z.val)) :=
  NativeMiddleSplitHomotopy.homotopy_length hr F s (splitInput z)

theorem original_length (hr : r ≤ 1) (F : ReversibleMetric n) (z : inputs n r) :
    SobolevLength.length F (right (prefixInner hr z.val)) =
      SobolevLength.length F (NativeOrderedDoubleCutGeometry.middle hr (prefixCommon z.val)) := by
  rw [original_eq]
  exact NativeMiddleSplitHomotopy.loop_length hr F (splitInput z)

theorem homotopy_basepoint (hr : r ≤ 1) (s : _root_.unitInterval) (z : inputs n r) :
    Finsler.CompactH1Alignment.basepoint (homotopy hr (s, z)) = (point z.val.val.1.val.2 : Ambient n) :=
  NativeMiddleSplitHomotopy.homotopy_basepoint hr s (splitInput z)

end
end Finsler.NativeSequentialPrefixMiddle
