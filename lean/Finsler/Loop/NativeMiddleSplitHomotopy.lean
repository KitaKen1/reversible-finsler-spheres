module

public import Finsler.Loop.NativeOrderedDoubleCutGeometry
public import Finsler.Topology.VariablePathConcat
public import Finsler.Topology.JoinSplitHomotopy

/-! A genuine strong-H1 homotopy changes ONLY the internal timing of
the COMMON middle loop. Every point has EXACTLY the original three-path
Finsler length and original basepoint. This is the reparametrization
needed by the retained middle output of the original prefix branch. -/
@[expose] public section
namespace Finsler.NativeMiddleSplitHomotopy
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1SelfCutNeighborhood Finsler.VariableJoinContinuity
open Finsler.NativeOrderedDoubleCutGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000
variable {n : ℕ} {r : ℝ}

abbrev inputs (n : ℕ) (r : ℝ) := Splits × domain n r

def tailPair (hr : r ≤ 1) (z : domain n r) : VariablePathConcat.Pairs n :=
  ⟨(rawMiddle z, lastArc hr z), rawMiddle_mem z, lastArc_mem hr z, middle_last_match hr z⟩

theorem continuous_tailPair (hr : r ≤ 1) : Continuous (tailPair (n := n) hr) :=
  ((continuous_rawMiddle (n := n)).prodMk (continuous_lastArc hr)).subtype_mk _

def tail (hr : r ≤ 1) (z : inputs n r) : Space n := VariablePathConcat.value (z.1, tailPair hr z.2)

theorem tail_mem (hr : r ≤ 1) (z : inputs n r) : tail hr z ∈ SpherePath n :=
  VariablePathConcat.value_mem _

theorem continuous_tail (hr : r ≤ 1) : Continuous (tail (n := n) hr) :=
  (VariablePathConcat.continuous_value (n := n)).comp
    (continuous_fst.prodMk ((continuous_tailPair hr).comp continuous_snd))

theorem first_tail_match (hr : r ≤ 1) (z : inputs n r) :
    continuousRepresentative (firstArc hr z.2) 1 = continuousRepresentative (tail hr z) 0 := by
  have h₀ : continuousRepresentative (firstArc hr z.2) 1 =
      (endpoint (firstCut hr z.2).val : Ambient n) :=
    (H1ShortArc.arc_mem (forward (firstCut hr z.2))).2.2
  have h₁ : continuousRepresentative (rawMiddle z.2) 0 =
      (endpoint (firstCut hr z.2).val : Ambient n) := representative_restrict_zero _ _ _ _
  have h₂ : continuousRepresentative (tail hr z) 0 = continuousRepresentative (rawMiddle z.2) 0 :=
    representative_concat_zero _ _ z.1.property.1 z.1.property.2
  exact h₀.trans (h₁.symm.trans h₂.symm)

def pair (hr : r ≤ 1) (z : inputs n r) : VariablePathConcat.Pairs n :=
  ⟨(firstArc hr z.2, tail hr z), firstArc_mem hr z.2, tail_mem hr z, first_tail_match hr z⟩

theorem continuous_pair (hr : r ≤ 1) : Continuous (pair (n := n) hr) :=
  (((continuous_firstArc hr).comp continuous_snd).prodMk (continuous_tail hr)).subtype_mk _

def data (hr : r ≤ 1) (z : inputs n r) : Space n :=
  VariablePathConcat.value (JoinSplitHomotopy.half, pair hr z)

theorem data_mem (hr : r ≤ 1) (z : inputs n r) : data hr z ∈ SpherePath n :=
  VariablePathConcat.value_mem _

theorem continuous_data (hr : r ≤ 1) : Continuous (data (n := n) hr) :=
  (VariablePathConcat.continuous_value (n := n)).comp (continuous_const.prodMk (continuous_pair hr))

theorem data_zero (hr : r ≤ 1) (z : inputs n r) :
    continuousRepresentative (data hr z) 0 = (point z.2.val.1 : Ambient n) :=
  (representative_concat_zero _ _ JoinSplitHomotopy.half.property.1 JoinSplitHomotopy.half.property.2).trans
    (H1ShortArc.arc_mem (forward (firstCut hr z.2))).2.1

theorem data_one (hr : r ≤ 1) (z : inputs n r) :
    continuousRepresentative (data hr z) 1 = (point z.2.val.1 : Ambient n) :=
  (representative_concat_one _ _ JoinSplitHomotopy.half.property.1 JoinSplitHomotopy.half.property.2 (first_tail_match hr z)).trans
    ((representative_concat_one _ _ z.1.property.1 z.1.property.2 (middle_last_match hr z.2)).trans
      (H1ShortArc.arc_mem (backward (lastCut hr z.2))).2.2)

def loop (hr : r ≤ 1) (z : inputs n r) : SphereLoop n :=
  ⟨⟨data hr z, (mem_periodicSubmodule_iff _).mpr ((data_one hr z).trans (data_zero hr z).symm)⟩,
    fun t => data_mem hr z t t.property⟩

theorem continuous_loop (hr : r ≤ 1) : Continuous (loop (n := n) hr) :=
  continuous_iff_continuousAt.mpr (fun _ => sphereLoop_tendsto_iff.mpr (continuous_data hr).continuousAt)

theorem loop_basepoint (hr : r ≤ 1) (z : inputs n r) :
    Finsler.CompactH1Alignment.basepoint (loop hr z) = (point z.2.val.1 : Ambient n) := data_zero hr z

theorem loop_length (hr : r ≤ 1) (F : ReversibleMetric n) (z : inputs n r) :
    SobolevLength.length F (loop hr z) = SobolevLength.length F (middle hr z.2) := by
  change H1PathLength.length F (data hr z) = _
  rw [middle_length]
  have ho := VariablePathConcat.length_value F (JoinSplitHomotopy.half, pair hr z)
  have hi := VariablePathConcat.length_value F (z.1, tailPair hr z.2)
  change H1PathLength.length F (data hr z) =
    H1PathLength.length F (firstArc hr z.2) + H1PathLength.length F (tail hr z) at ho
  change H1PathLength.length F (tail hr z) =
    H1PathLength.length F (rawMiddle z.2) + H1PathLength.length F (lastArc hr z.2) at hi
  rw [ho, hi]
  ring

theorem half_eq (hr : r ≤ 1) (z : domain n r) :
    loop hr (JoinSplitHomotopy.half, z) = middle hr z := by
  apply sphereLoop_data_injective
  rfl

def initialMap (hr : r ≤ 1) : C(inputs n r, SphereLoop n) := ⟨loop hr, continuous_loop hr⟩

def targetMap (hr : r ≤ 1) : C(inputs n r, SphereLoop n) :=
  ⟨fun z => middle hr z.2, (continuous_middle hr).comp continuous_snd⟩

def homotopy (hr : r ≤ 1) : (initialMap (n := n) hr).Homotopy (targetMap hr) where
  toFun z := loop hr (JoinSplitHomotopy.interpolate z.2.1 JoinSplitHomotopy.half z.1, z.2.2)
  continuous_toFun := by
    have hs : Continuous (fun z : _root_.unitInterval × inputs n r =>
        JoinSplitHomotopy.interpolate z.2.1 JoinSplitHomotopy.half z.1) := by
      unfold JoinSplitHomotopy.interpolate
      fun_prop
    exact (continuous_loop hr).comp (hs.prodMk (continuous_snd.comp continuous_snd))
  map_zero_left z := by
    change loop hr (JoinSplitHomotopy.interpolate z.1 JoinSplitHomotopy.half 0, z.2) = _
    rw [JoinSplitHomotopy.interpolate_zero]
    rfl
  map_one_left z := by
    change loop hr (JoinSplitHomotopy.interpolate z.1 JoinSplitHomotopy.half 1, z.2) = _
    rw [JoinSplitHomotopy.interpolate_one]
    exact half_eq hr z.2

theorem homotopy_length (hr : r ≤ 1) (F : ReversibleMetric n)
    (s : _root_.unitInterval) (z : inputs n r) :
    SobolevLength.length F (homotopy hr (s, z)) = SobolevLength.length F (middle hr z.2) :=
  loop_length hr F _

theorem homotopy_basepoint (hr : r ≤ 1) (s : _root_.unitInterval) (z : inputs n r) :
    Finsler.CompactH1Alignment.basepoint (homotopy hr (s, z)) = (point z.2.val.1 : Ambient n) :=
  loop_basepoint hr _

end
end Finsler.NativeMiddleSplitHomotopy
