module

public import Finsler.Loop.NativeSequentialCutOuterOutputs
public import Finsler.Loop.NativeHalfConcatPrefix
public import Finsler.Topology.ThreePathLoop
public import Finsler.Topology.FirstHalfRebracket

/-! The OTHER ORIGINAL middle output: the tested loop after cutting
the suffix half of the original retained loop. Its three actual pieces
have the REAL split1/(1+u). On u>0, interpolate positive three-path
splits to the exact common middle timing, preserving Finsler length
and basepoint throughout. The excluded u=0 seam remains explicit. -/
@[expose] public section
namespace Finsler.NativeSequentialSuffixMiddle
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
set_option maxHeartbeats 900000
variable {n : ℕ} {r : ℝ}

abbrev inputs (n : ℕ) (r : ℝ) := {z : suffixDomain n r | 0 < (z.val.2 : ℝ)}

def time (z : inputs n r) : NativeHalfConcatPrefix.Times :=
  ⟨z.val.val.2, z.property, z.val.val.2.property.2⟩

theorem continuous_time : Continuous (time (n := n) (r := r)) := by unfold time; fun_prop

theorem middle_restriction (z : inputs n r) :
    restrict (suffixPath z.val.val.1) (by norm_num) z.val.val.2.property z.val.val.2.property.1 =
      NativeOrderedDoubleCutGeometry.rawMiddle (suffixCommon z.val) := by
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_restrict _ _ _ _ hτ, suffixPath,
    representative_restrict _ _ _ _ (aff_mem_Icc (by norm_num) z.val.val.2.property hτ),
    NativeOrderedDoubleCutGeometry.rawMiddle, representative_restrict _ _ _ _ hτ]
  congr 1
  change aff (z.val.val.1.val.1 : ℝ) 1 (aff 0 (z.val.val.2 : ℝ) τ) =
    aff (z.val.val.1.val.1 : ℝ) ((z.val.val.1.val.1 : ℝ) + (1 - z.val.val.1.val.1) * z.val.val.2) τ
  dsimp [aff]
  ring

theorem prefix_data (hr : r ≤ 1) (z : inputs n r) : prefixPath (suffixInner hr z.val) =
    concat (NativeOrderedDoubleCutGeometry.firstArc hr (suffixCommon z.val))
      (NativeOrderedDoubleCutGeometry.rawMiddle (suffixCommon z.val))
      (NativeHalfConcatPrefix.frontSplit (time z)).property.1
      (NativeHalfConcatPrefix.frontSplit (time z)).property.2 := by
  have h := NativeHalfConcatPrefix.prefix_path
    (H1ShortArc.arc (point z.val.val.1.val.2) (endpoint z.val.val.1.val))
    (suffixPath z.val.val.1) (time z) (right_match z.val.val.1)
  change prefixPath (suffixInner hr z.val) =
    concat (NativeOrderedDoubleCutGeometry.firstArc hr (suffixCommon z.val))
      (restrict (suffixPath z.val.val.1) (by norm_num) z.val.val.2.property z.val.val.2.property.1)
      (NativeHalfConcatPrefix.frontSplit (time z)).property.1
      (NativeHalfConcatPrefix.frontSplit (time z)).property.2 at h
  exact h.trans (congrArg (fun w : Space n => concat
    (NativeOrderedDoubleCutGeometry.firstArc hr (suffixCommon z.val)) w
    (NativeHalfConcatPrefix.frontSplit (time z)).property.1
    (NativeHalfConcatPrefix.frontSplit (time z)).property.2) (middle_restriction z))

def data (hr : r ≤ 1) (z : inputs n r) : ThreePathLoop.Data n := by
  let c := suffixCommon z.val
  refine ⟨(NativeOrderedDoubleCutGeometry.firstArc hr c,
      NativeOrderedDoubleCutGeometry.rawMiddle c, NativeOrderedDoubleCutGeometry.lastArc hr c),
    NativeOrderedDoubleCutGeometry.firstArc_mem hr c,
    NativeOrderedDoubleCutGeometry.rawMiddle_mem c,
    NativeOrderedDoubleCutGeometry.lastArc_mem hr c, ?_,
    NativeOrderedDoubleCutGeometry.middle_last_match hr c, ?_⟩
  · have h₀ : continuousRepresentative (NativeOrderedDoubleCutGeometry.rawMiddle c) 0 =
        (endpoint (NativeOrderedDoubleCutGeometry.firstCut hr c).val : Ambient n) :=
      representative_restrict_zero _ _ _ _
    exact (H1ShortArc.arc_mem (forward (NativeOrderedDoubleCutGeometry.firstCut hr c))).2.2.trans h₀.symm
  · exact (H1ShortArc.arc_mem (backward (NativeOrderedDoubleCutGeometry.lastCut hr c))).2.2.trans
      (H1ShortArc.arc_mem (forward (NativeOrderedDoubleCutGeometry.firstCut hr c))).2.1.symm

theorem continuous_data (hr : r ≤ 1) : Continuous (data (n := n) hr) := by
  have hc : Continuous (fun z : inputs n r => suffixCommon z.val) :=
    continuous_suffixCommon.comp continuous_subtype_val
  exact (((NativeOrderedDoubleCutGeometry.continuous_firstArc hr).comp hc).prodMk
    (((NativeOrderedDoubleCutGeometry.continuous_rawMiddle (n := n)).comp hc).prodMk
      ((NativeOrderedDoubleCutGeometry.continuous_lastArc hr).comp hc))).subtype_mk _

def zeroTime : FirstHalfSplits.Times := ⟨0, le_rfl, zero_lt_one⟩

/-- Rebracket abstract paths before substituting the geometric input. -/
private theorem common_value (d : ThreePathLoop.Data n) :
    ((ThreePathLoop.loop
      ((FirstHalfSplits.inner zeroTime, FirstHalfSplits.outer zeroTime), d)).data : Space n) =
      concat d.val.1 (concat d.val.2.1 d.val.2.2
        (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num))
        (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) := by
  have he := FirstHalfRebracket.concat_eq d.val.1 d.val.2.1 d.val.2.2 zeroTime
    d.property.2.2.2.1 d.property.2.2.2.2.1
  have hk : HalfConcatRestriction.tailSplit zeroTime = JoinSplitHomotopy.half := by
    apply Subtype.ext
    norm_num [HalfConcatRestriction.tailSplit, zeroTime, JoinSplitHomotopy.half]
  change concat (concat d.val.1 d.val.2.1
      (FirstHalfSplits.inner zeroTime).property.1
      (FirstHalfSplits.inner zeroTime).property.2) d.val.2.2
      (FirstHalfSplits.outer zeroTime).property.1
      (FirstHalfSplits.outer zeroTime).property.2 = _
  calc
    _ = concat d.val.1 (concat d.val.2.1 d.val.2.2
        (HalfConcatRestriction.tailSplit zeroTime).property.1
        (HalfConcatRestriction.tailSplit zeroTime).property.2)
        (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) := he.symm
    _ = _ := congrArg (fun k : Splits => concat d.val.1
      (concat d.val.2.1 d.val.2.2 k.property.1 k.property.2)
      (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)) hk

theorem common_eq (hr : r ≤ 1) (z : inputs n r) :
    ThreePathLoop.loop ((FirstHalfSplits.inner zeroTime, FirstHalfSplits.outer zeroTime), data hr z) =
      NativeOrderedDoubleCutGeometry.middle hr (suffixCommon z.val) := by
  apply sphereLoop_data_injective
  exact common_value (data hr z)

theorem original_eq (hr : r ≤ 1) (z : inputs n r) :
    left (suffixInner hr z.val) = ThreePathLoop.loop
      ((NativeHalfConcatPrefix.frontSplit (time z), JoinSplitHomotopy.half), data hr z) := by
  apply sphereLoop_data_injective
  change concat (prefixPath (suffixInner hr z.val))
    (H1ShortArc.arc (endpoint (suffixInner hr z.val).val) (point (suffixInner hr z.val).val.2))
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) = _
  rw [prefix_data, suffix_endpoint, suffix_point]
  rfl

def originalMap (hr : r ≤ 1) : C(inputs n r, SphereLoop n) :=
  ⟨fun z => left (suffixInner hr z.val),
    (continuous_left (n := n)).comp ((continuous_suffixInner hr).comp continuous_subtype_val)⟩

def commonMap (hr : r ≤ 1) : C(inputs n r, SphereLoop n) :=
  ⟨fun z => NativeOrderedDoubleCutGeometry.middle hr (suffixCommon z.val),
    (NativeOrderedDoubleCutGeometry.continuous_middle hr).comp
      (continuous_suffixCommon.comp continuous_subtype_val)⟩

def homotopy (hr : r ≤ 1) : (originalMap (n := n) (r := r) hr).Homotopy (commonMap hr) where
  toFun z := ThreePathLoop.loop
    ((JoinSplitHomotopy.interpolate (NativeHalfConcatPrefix.frontSplit (time z.2)) (FirstHalfSplits.inner zeroTime) z.1,
      JoinSplitHomotopy.interpolate JoinSplitHomotopy.half (FirstHalfSplits.outer zeroTime) z.1), data hr z.2)
  continuous_toFun := by
    have hi : Continuous (fun z : _root_.unitInterval × inputs n r =>
        JoinSplitHomotopy.interpolate (NativeHalfConcatPrefix.frontSplit (time z.2)) (FirstHalfSplits.inner zeroTime) z.1) := by
      have hfront : Continuous (fun z : _root_.unitInterval × inputs n r =>
          NativeHalfConcatPrefix.frontSplit (time z.2)) :=
        NativeHalfConcatPrefix.continuous_frontSplit.comp (continuous_time.comp continuous_snd)
      unfold JoinSplitHomotopy.interpolate
      exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp hfront)).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).subtype_mk _
    have ho := (JoinSplitHomotopy.continuous_interpolate JoinSplitHomotopy.half
      (FirstHalfSplits.outer zeroTime)).comp (continuous_fst (X := _root_.unitInterval) (Y := inputs n r))
    exact (ThreePathLoop.continuous_loop (n := n)).comp
      ((hi.prodMk ho).prodMk ((continuous_data hr).comp continuous_snd))
  map_zero_left z := by
    change ThreePathLoop.loop ((JoinSplitHomotopy.interpolate _ _ 0, JoinSplitHomotopy.interpolate _ _ 0), data hr z) = _
    rw [JoinSplitHomotopy.interpolate_zero, JoinSplitHomotopy.interpolate_zero]
    exact (original_eq hr z).symm
  map_one_left z := by
    change ThreePathLoop.loop ((JoinSplitHomotopy.interpolate _ _ 1, JoinSplitHomotopy.interpolate _ _ 1), data hr z) = _
    rw [JoinSplitHomotopy.interpolate_one, JoinSplitHomotopy.interpolate_one]
    exact common_eq hr z

theorem homotopy_length (hr : r ≤ 1) (F : ReversibleMetric n)
    (s : _root_.unitInterval) (z : inputs n r) :
    SobolevLength.length F (homotopy hr (s, z)) =
      SobolevLength.length F (NativeOrderedDoubleCutGeometry.middle hr (suffixCommon z.val)) :=
  (ThreePathLoop.length_loop F _).trans (NativeOrderedDoubleCutGeometry.middle_length hr F (suffixCommon z.val)).symm

theorem original_length (hr : r ≤ 1) (F : ReversibleMetric n) (z : inputs n r) :
    SobolevLength.length F (left (suffixInner hr z.val)) =
      SobolevLength.length F (NativeOrderedDoubleCutGeometry.middle hr (suffixCommon z.val)) := by
  rw [original_eq]
  exact (ThreePathLoop.length_loop F _).trans
    (NativeOrderedDoubleCutGeometry.middle_length hr F (suffixCommon z.val)).symm

theorem homotopy_basepoint (hr : r ≤ 1) (s : _root_.unitInterval) (z : inputs n r) :
    Finsler.CompactH1Alignment.basepoint (homotopy hr (s, z)) = (point z.val.val.1.val.2 : Ambient n) :=
  (ThreePathLoop.loop_zero _).trans
    (H1ShortArc.arc_mem (forward (NativeOrderedDoubleCutGeometry.firstCut hr (suffixCommon z.val)))).2.1

end
end Finsler.NativeSequentialSuffixMiddle
