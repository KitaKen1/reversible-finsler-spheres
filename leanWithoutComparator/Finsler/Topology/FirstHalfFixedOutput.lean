module

public import Finsler.Topology.FirstHalfJoinedCut
public import Finsler.Topology.FirstHalfRebracket

/-! The original first-half joined self-cut is homotopic to joining its
first retained loop with the second input, with the actual tested output
fixed and exactly the same retained length throughout. Time-chain seam
comparisons and the other original homotopy families remain separate. -/

@[expose] public section
namespace Finsler.FirstHalfFixedOutput

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1LoopJoin Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase
open Finsler.SobolevConcat Finsler.FirstHalfRetainedHomotopy Finsler.FirstHalfJoinedCut
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {n : ℕ}

theorem retained_eq (z : inputs n) : right (joinedTube z) = retained (0, z) := by
  rw [retained_zero]
  apply sphereLoop_data_injective
  change ((right (joinedTube z)).data : Space n) =
    ((ThreePathLoop.loop ((FirstHalfSplits.inner (time z), FirstHalfSplits.outer (time z)), data z)).data : Space n)
  rw [retained_data]
  exact FirstHalfRebracket.concat_eq
    (H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val)) (suffixPath z.val.1)
    (z.val.2.data : Space n) (time z) (right_match z.val.1) (data z).property.2.2.2.2.1

def originalMap : C(inputs n, SphereLoop n) :=
  ⟨fun z => right (joinedTube z), continuous_right.comp continuous_joinedTube⟩

def homotopy : (originalMap (n := n)).Homotopy targetMap where
  toFun := retained
  continuous_toFun := continuous_retained
  map_zero_left z := (retained_eq z).symm
  map_one_left z := retained_one z

def family : C(_root_.unitInterval × inputs n, SphereLoop n × SphereLoop n) :=
  ⟨fun z => (left (joinedTube z.2), homotopy z),
    ((continuous_left.comp continuous_joinedTube).comp continuous_snd).prodMk continuous_retained⟩

theorem tested_fixed (s : _root_.unitInterval) (z : inputs n) :
    (family (s, z)).1 = left z.val.1 := tested_eq z

theorem family_zero (z : inputs n) :
    family (0, z) = (left (joinedTube z), right (joinedTube z)) :=
  Prod.ext rfl (retained_eq z).symm

theorem family_one (z : inputs n) :
    family (1, z) = (left z.val.1,
      join (1 / 2) (by norm_num) (by norm_num) (right z.val.1) z.val.2
        ((basepoint_right z.val.1).trans z.property.2)) :=
  Prod.ext (tested_eq z) (retained_one z)

theorem length_original (F : ReversibleMetric n) (s : _root_.unitInterval) (z : inputs n) :
    SobolevLength.length F (homotopy (s, z)) = SobolevLength.length F (right (joinedTube z)) :=
  (retained_length F s z).trans ((retained_length F 0 z).symm.trans
    (congrArg (SobolevLength.length F) (retained_eq z)).symm)

def filteredInputs (F : ReversibleMetric n) (A : ℝ) : Set (inputs n) :=
  {z | SobolevLength.length F (right (joinedTube z)) < A}

def filteredFamily (F : ReversibleMetric n) (A : ℝ) :
    C(_root_.unitInterval × filteredInputs F A, {u : SphereLoop n | SobolevLength.length F u < A}) := by
  refine ⟨fun z => ⟨homotopy (z.1, z.2.val), ?_⟩, ?_⟩
  · change SobolevLength.length F (homotopy (z.1, z.2.val)) < A
    rw [length_original]
    exact z.2.property
  · have hc : Continuous (fun z : _root_.unitInterval × filteredInputs F A =>
        homotopy (z.1, z.2.val)) :=
      continuous_retained.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact hc.subtype_mk _

end
end Finsler.FirstHalfFixedOutput
