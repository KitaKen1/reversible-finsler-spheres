module

public import Finsler.Topology.ThreePathLoop
public import Finsler.Topology.FirstHalfSplits
public import Finsler.Analysis.H1SelfCutNeighborhood

/-! The actual first-half retained three-piece homotopy, with fixed
tested loop and exact length. Identification of the initial timing with
the original joined-loop self-cut is a separate chain/geometry obligation. -/

@[expose] public section
namespace Finsler.FirstHalfRetainedHomotopy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevConcat Finsler.SobolevSpherePath Finsler.SobolevAffine
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1JoinContinuity
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {n : ℕ}

def inputs (n : ℕ) : Set (tube n × SphereLoop n) :=
  {z | (z.1.val.1 : ℝ) < 1 ∧ basepoint z.1.val.2 = basepoint z.2}

def time (z : inputs n) : FirstHalfSplits.Times :=
  ⟨z.val.1.val.1, z.val.1.val.1.property.1, z.property.1⟩

theorem continuous_time : Continuous (time (n := n)) := by
  have hz : Continuous (fun z : inputs n => z.val.1) := continuous_fst.comp continuous_subtype_val
  exact (continuous_subtype_val.comp
    (continuous_fst.comp (continuous_subtype_val.comp hz))).subtype_mk _

def data (z : inputs n) : ThreePathLoop.Data n := by
  have hs : continuousRepresentative (suffixPath z.val.1) 1 = basepoint z.val.1.val.2 :=
    (representative_restrict_one _ z.val.1.val.1.property (by norm_num)
      z.val.1.val.1.property.2).trans (periodic_trace z.val.1.val.2)
  refine ⟨(H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val),
    suffixPath z.val.1, (z.val.2.data : Space n)),
    (H1ShortArc.arc_mem (forward z.val.1)).1, suffix_mem z.val.1,
    sphereLoop_mem z.val.2, right_match z.val.1, hs.trans z.property.2, ?_⟩
  exact (periodic_trace z.val.2).trans
    (z.property.2.symm.trans (H1ShortArc.arc_mem (forward z.val.1)).2.1.symm)

theorem continuous_data : Continuous (data (n := n)) := by
  have hz : Continuous (fun z : inputs n => z.val.1) := continuous_fst.comp continuous_subtype_val
  have hy : Continuous (fun z : inputs n => z.val.2) := continuous_snd.comp continuous_subtype_val
  have ha := H1ShortArc.continuous_arc.comp (continuous_forward.comp hz)
  have hs := continuous_suffix.comp hz
  have hw := (sphereLoop_data_isometry n).continuous.comp hy
  exact (ha.prodMk (hs.prodMk hw)).subtype_mk _

def retained (z : _root_.unitInterval × inputs n) : SphereLoop n :=
  ThreePathLoop.loop (FirstHalfSplits.splits (z.1, time z.2), data z.2)

theorem continuous_retained : Continuous (retained (n := n)) :=
  ThreePathLoop.continuous_loop.comp
    ((FirstHalfSplits.continuous_splits.comp
      (continuous_fst.prodMk (continuous_time.comp continuous_snd))).prodMk
        (continuous_data.comp continuous_snd))

def tested (z : _root_.unitInterval × inputs n) : SphereLoop n := left z.2.val.1

theorem continuous_tested : Continuous (tested (n := n)) :=
  continuous_left.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))

theorem tested_fixed (s : _root_.unitInterval) (z : inputs n) : tested (s, z) = left z.val.1 := rfl

theorem retained_zero (z : inputs n) :
    retained (0, z) = ThreePathLoop.loop ((FirstHalfSplits.inner (time z),
      FirstHalfSplits.outer (time z)), data z) := by
  unfold retained
  rw [FirstHalfSplits.splits_zero]

theorem retained_one (z : inputs n) :
    retained (1, z) = join (1 / 2) (by norm_num) (by norm_num) (right z.val.1) z.val.2
      ((basepoint_right z.val.1).trans z.property.2) := by
  unfold retained
  rw [FirstHalfSplits.splits_one]
  apply sphereLoop_data_injective
  rfl

theorem retained_basepoint (s : _root_.unitInterval) (z : inputs n) :
    basepoint (retained (s, z)) = basepoint z.val.1.val.2 :=
  (ThreePathLoop.loop_zero _).trans (H1ShortArc.arc_mem (forward z.val.1)).2.1

theorem retained_length (F : ReversibleMetric n) (s : _root_.unitInterval) (z : inputs n) :
    SobolevLength.length F (retained (s, z)) =
      SobolevLength.length F (right z.val.1) + SobolevLength.length F z.val.2 := by
  rw [length_right]
  exact ThreePathLoop.length_loop F _

def joinedPair (z : inputs n) : composable n :=
  ⟨(right z.val.1, z.val.2), (basepoint_right z.val.1).trans z.property.2⟩

theorem continuous_joinedPair : Continuous (joinedPair (n := n)) :=
  ((continuous_right.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

def initialMap : C(inputs n, SphereLoop n) :=
  ⟨fun z => retained (0, z), continuous_retained.comp (continuous_const.prodMk continuous_id)⟩

def targetMap : C(inputs n, SphereLoop n) :=
  (joinMap (1 / 2) (by norm_num) (by norm_num)).comp ⟨joinedPair, continuous_joinedPair⟩

def homotopy : (initialMap (n := n)).Homotopy targetMap where
  toFun := retained
  continuous_toFun := continuous_retained
  map_zero_left _ := rfl
  map_one_left z := retained_one z

end
end Finsler.FirstHalfRetainedHomotopy
