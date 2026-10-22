module

public import Finsler.Loop.NativeNearCutClocks
public import Finsler.Loop.H1PathRepresentativeCalculus
public import Finsler.Loop.ShortArcUniformEndpoint
public import Finsler.Loop.CloseSphereHomotopy

/-! Rejoin the ORIGINAL two H1 self-cut outputs. On a fixed genuine
near tube the rejoined representative is uniformly close to the
original loop paused at its cut point. No arc reversal identity is assumed. -/
@[expose] public section
namespace Finsler.NativeNearCutRejoining
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevConcat
open Finsler.CompactH1Alignment Finsler.NativeSelfCutSegmentClocks
open Finsler.NativeNearCutClocks
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
local notation "I" => ClosedInterval

def domain (n : ℕ) : TopCat :=
  TopCat.of {z : I × SphereLoop n // ‖(endpoint z : Ambient n) - point z.2‖ < 1 / 8}

def input {n : ℕ} (z : domain n) : tube n :=
  ⟨z.val, z.property.trans (by norm_num)⟩

theorem continuous_input (n : ℕ) : Continuous (input (n := n)) :=
  continuous_subtype_val.subtype_mk _

def joined {n : ℕ} (z : domain n) : SphereLoop n :=
  H1LoopJoin.join (1 / 2) (by norm_num) (by norm_num) (left (input z)) (right (input z))
    ((basepoint_left (input z)).trans (basepoint_right (input z)).symm)

theorem continuous_joined (n : ℕ) : Continuous (joined (n := n)) := by
  have hd := H1PathRepresentativeCalculus.continuous_halfConcat
    (fun z : domain n => leftData (input z)) (fun z : domain n => rightData (input z))
    (continuous_leftData.comp (continuous_input n)) (continuous_rightData.comp (continuous_input n))
    (fun z => (leftData_one (input z)).trans (rightData_zero (input z)).symm)
  apply continuous_iff_continuousAt.mpr
  intro z
  exact sphereLoop_tendsto_iff.mpr hd.continuousAt

theorem joined_first {n : ℕ} (z : domain n) (t : I) :
    sphereRepresentative (joined z) (firstHalf t) = sphereRepresentative (left (input z)) t := by
  apply Subtype.ext
  change continuousRepresentative (concat (leftData (input z)) (rightData (input z))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)) ((t : ℝ) / 2) = _
  rw [representative_concat_left _ _ (by norm_num) (by norm_num)
    (by constructor <;> linarith [t.property.1, t.property.2])]
  congr 1
  ring

theorem joined_second {n : ℕ} (z : domain n) (t : I) :
    sphereRepresentative (joined z) (secondHalf t) = sphereRepresentative (right (input z)) t := by
  apply Subtype.ext
  change continuousRepresentative (concat (leftData (input z)) (rightData (input z))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)) ((1 + (t : ℝ)) / 2) = _
  rw [representative_concat_right _ _ (by norm_num) (by norm_num)
    ((leftData_one (input z)).trans (rightData_zero (input z)).symm)
    (by constructor <;> linarith [t.property.1, t.property.2])]
  congr 1
  norm_num [rightMap]
  ring

theorem joined_zero {n : ℕ} (z : domain n) :
    sphereRepresentative (joined z) 0 = sphereRepresentative z.val.2 0 := by
  apply Subtype.ext
  exact (H1LoopJoin.basepoint_join _ _ _ _ _ _).trans (basepoint_left (input z))

theorem joined_one {n : ℕ} (z : domain n) :
    sphereRepresentative (joined z) 1 = sphereRepresentative z.val.2 1 := by
  exact (sphereRepresentative_endpoints (joined z)).trans
    ((joined_zero z).trans (sphereRepresentative_endpoints z.val.2).symm)

theorem uniformly_close {n : ℕ} (z : domain n) (t : I) :
    dist (sphereRepresentative (joined z) t)
      (sphereRepresentative z.val.2 (splice z.val.1 t)) < 1 := by
  rcases half_cases t with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases half_cases a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [joined_first, left_prefix, first_first]
      exact zero_lt_one.trans_le' (le_of_eq (dist_self _))
    · rw [joined_first, first_second, Subtype.dist_eq, dist_eq_norm, left_closing_arc]
      have hb := ShortArcUniformEndpoint.distance_start (backward (input z)) b
      have he : ‖continuousRepresentative
          (H1ShortArc.arc (endpoint z.val) (point z.val.2)) b - (endpoint z.val : Ambient n)‖ ≤
          6 * ‖(endpoint z.val : Ambient n) - point z.val.2‖ := by
        simpa only [backward, input, norm_sub_rev] using hb
      exact he.trans_lt (by linarith [z.property])
  · rcases half_cases a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [joined_second, second_first, Subtype.dist_eq, dist_eq_norm, right_closing_arc]
      have he := ShortArcUniformEndpoint.distance_finish (forward (input z)) b
      exact he.trans_lt (by change 7 * ‖(endpoint z.val : Ambient n) - point z.val.2‖ < 1; linarith [z.property])
    · rw [joined_second, right_suffix, second_second]
      exact zero_lt_one.trans_le' (le_of_eq (dist_self _))

end
end Finsler.NativeNearCutRejoining
