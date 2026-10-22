module

public import Finsler.Topology.FirstHalfRetainedHomotopy
public import Finsler.Topology.HalfConcatRestriction

/-! The actual self-cut of a half-time joined H1 loop in its first half.
The tested loop agrees literally with the cut of the first input. The
retained graph is the specified right-associated three-piece path. -/

@[expose] public section
namespace Finsler.FirstHalfJoinedCut

open Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1JoinContinuity
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevConcat
open Finsler.FirstHalfRetainedHomotopy
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {n : ℕ}

def originalPair (z : inputs n) : composable n :=
  ⟨(z.val.1.val.2, z.val.2), z.property.2⟩

theorem continuous_originalPair : Continuous (originalPair (n := n)) :=
  ((continuous_snd.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

def joinedLoop (z : inputs n) : SphereLoop n :=
  join (1 / 2) (by norm_num) (by norm_num) z.val.1.val.2 z.val.2 z.property.2

theorem continuous_joinedLoop : Continuous (joinedLoop (n := n)) := by
  have hc := (continuous_join (n := n) (1 / 2) (by norm_num) (by norm_num)).comp
    (continuous_originalPair (n := n))
  exact hc.congr (fun z => rfl)

def joinedTime (z : inputs n) : ClosedInterval := HalfConcatRestriction.half z.val.1.val.1

theorem continuous_joinedTime : Continuous (joinedTime (n := n)) :=
  ((continuous_subtype_val.comp FirstHalfRetainedHomotopy.continuous_time).div_const 2).subtype_mk _

theorem joined_point (z : inputs n) : point (joinedLoop z) = point z.val.1.val.2 := by
  apply Subtype.ext
  exact basepoint_join (1 / 2) (by norm_num) (by norm_num) _ _ z.property.2

theorem joined_endpoint (z : inputs n) :
    endpoint (joinedTime z, joinedLoop z) = endpoint z.val.1.val := by
  apply Subtype.ext
  exact HalfConcatRestriction.evaluate (z.val.1.val.2.data : Space n) (z.val.2.data : Space n) z.val.1.val.1

def joinedTube (z : inputs n) : tube n :=
  ⟨(joinedTime z, joinedLoop z), by
    change ‖(endpoint (joinedTime z, joinedLoop z) : Ambient n) - point (joinedLoop z)‖ < 1
    rw [joined_endpoint, joined_point]
    exact z.val.1.property⟩

theorem continuous_joinedTube : Continuous (joinedTube (n := n)) :=
  (continuous_joinedTime.prodMk continuous_joinedLoop).subtype_mk _

theorem prefix_path (z : inputs n) : prefixPath (joinedTube z) = prefixPath z.val.1 :=
  HalfConcatRestriction.prefix_path (z.val.1.val.2.data : Space n) (z.val.2.data : Space n) z.val.1.val.1

theorem suffix_path (z : inputs n) : suffixPath (joinedTube z) =
    concat (suffixPath z.val.1) (z.val.2.data : Space n)
      (HalfConcatRestriction.tailSplit (time z)).property.1
      (HalfConcatRestriction.tailSplit (time z)).property.2 :=
  HalfConcatRestriction.suffix (z.val.1.val.2.data : Space n) (z.val.2.data : Space n) (time z)
    (end_match _ _ z.property.2)

theorem tested_eq (z : inputs n) : left (joinedTube z) = left z.val.1 := by
  apply sphereLoop_data_injective
  change concat (prefixPath (joinedTube z))
    (H1ShortArc.arc (endpoint (joinedTime z, joinedLoop z)) (point (joinedLoop z)))
      (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) = _
  rw [prefix_path, joined_endpoint, joined_point]
  rfl

theorem retained_data (z : inputs n) :
    ((right (joinedTube z)).data : Space n) =
      concat (H1ShortArc.arc (point z.val.1.val.2) (endpoint z.val.1.val))
        (concat (suffixPath z.val.1) (z.val.2.data : Space n)
          (HalfConcatRestriction.tailSplit (time z)).property.1
          (HalfConcatRestriction.tailSplit (time z)).property.2)
        (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) := by
  change concat (H1ShortArc.arc (point (joinedLoop z)) (endpoint (joinedTime z, joinedLoop z)))
    (suffixPath (joinedTube z)) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) = _
  rw [joined_point, joined_endpoint, suffix_path]

end
end Finsler.FirstHalfJoinedCut
