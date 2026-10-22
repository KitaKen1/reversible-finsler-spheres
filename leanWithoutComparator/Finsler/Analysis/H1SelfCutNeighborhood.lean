module

public import Finsler.Analysis.H1ShortArc
public import Finsler.Analysis.H1AffineRestrictionContinuity
public import Finsler.Analysis.H1ConcatContinuity
public import Finsler.Analysis.H1FiberBase
public import Finsler.Analysis.H1LoopJoin

/-! The actual two short-arc self-cut maps on an open evaluation tube. Prefix
and suffixPath are each assigned half the time; the closing arc gets the other
half. All times, including 0 and 1, use the same continuous construction.
These maps alone do not define the supported Thom chain operation D_T. -/

@[expose] public section
namespace Finsler.H1SelfCutNeighborhood

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1FiberBase Finsler.CompactH1Alignment
open Finsler.H1AffineRestrictionContinuity Finsler.H1ConcatContinuity
open Finsler.SobolevEnergy Finsler.H1LoopJoin
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {n : ℕ}

def endpoint (z : ClosedInterval × SphereLoop n) : Sphere n := sphereRepresentative z.2 z.1

theorem continuous_endpoint : Continuous (endpoint (n := n)) := by
  have hu : Continuous (fun z : ClosedInterval × SphereLoop n =>
      representativeL n (z.2.data : Space n)) :=
    (representativeL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp continuous_snd)
  exact (continuous_eval.comp (hu.prodMk continuous_fst)).subtype_mk _

def tube (n : ℕ) : Set (ClosedInterval × SphereLoop n) :=
  {z | ‖(endpoint z : Ambient n) - (point z.2 : Ambient n)‖ < 1}

theorem tube_open : IsOpen (tube n) :=
  isOpen_lt ((continuous_subtype_val.comp continuous_endpoint).sub
    (continuous_subtype_val.comp (continuous_point.comp continuous_snd))).norm continuous_const

def forward (z : tube n) : H1ShortArc.pairs n :=
  ⟨(point z.val.2, endpoint z.val), z.property⟩

def backward (z : tube n) : H1ShortArc.pairs n :=
  ⟨(endpoint z.val, point z.val.2), by
    change ‖(point z.val.2 : Ambient n) - (endpoint z.val : Ambient n)‖ < 1
    rw [norm_sub_rev]
    exact z.property⟩

theorem continuous_forward : Continuous (forward (n := n)) :=
  ((continuous_point.comp (continuous_snd.comp continuous_subtype_val)).prodMk
    (continuous_endpoint.comp continuous_subtype_val)).subtype_mk _

theorem continuous_backward : Continuous (backward (n := n)) :=
  ((continuous_endpoint.comp continuous_subtype_val).prodMk
    (continuous_point.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

def prefixPath (z : tube n) : Space n :=
  restrict (z.val.2.data : Space n) (by norm_num) z.val.1.property z.val.1.property.1

def suffixPath (z : tube n) : Space n :=
  restrict (z.val.2.data : Space n) z.val.1.property (by norm_num) z.val.1.property.2

theorem prefix_mem (z : tube n) : prefixPath z ∈ SpherePath n :=
  restrict_mem (sphereLoop_mem z.val.2) (by norm_num) z.val.1.property z.val.1.property.1

theorem suffix_mem (z : tube n) : suffixPath z ∈ SpherePath n :=
  restrict_mem (sphereLoop_mem z.val.2) z.val.1.property (by norm_num) z.val.1.property.2

theorem continuous_prefix : Continuous (prefixPath (n := n)) := by
  have ht : Continuous (fun z : tube n => z.val.1) := continuous_fst.comp continuous_subtype_val
  have hu : Continuous (fun z : tube n => (z.val.2.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hp : Continuous (fun z : tube n =>
      ((⟨(0, z.val.1), z.val.1.property.1⟩ : Intervals), (z.val.2.data : Space n))) :=
    ((continuous_const.prodMk ht).subtype_mk _).prodMk hu
  exact continuous_restriction.comp hp

theorem continuous_suffix : Continuous (suffixPath (n := n)) := by
  have ht : Continuous (fun z : tube n => z.val.1) := continuous_fst.comp continuous_subtype_val
  have hu : Continuous (fun z : tube n => (z.val.2.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hp : Continuous (fun z : tube n =>
      ((⟨(z.val.1, 1), z.val.1.property.2⟩ : Intervals), (z.val.2.data : Space n))) :=
    ((ht.prodMk continuous_const).subtype_mk _).prodMk hu
  exact continuous_restriction.comp hp

theorem left_match (z : tube n) : continuousRepresentative (prefixPath z) 1 =
    continuousRepresentative (H1ShortArc.arc (endpoint z.val) (point z.val.2)) 0 := by
  exact (representative_restrict_one (z.val.2.data : Space n) (by norm_num)
    z.val.1.property z.val.1.property.1).trans (H1ShortArc.arc_mem (backward z)).2.1.symm

theorem right_match (z : tube n) :
    continuousRepresentative (H1ShortArc.arc (point z.val.2) (endpoint z.val)) 1 =
      continuousRepresentative (suffixPath z) 0 :=
  (H1ShortArc.arc_mem (forward z)).2.2.trans
    (representative_restrict_zero (z.val.2.data : Space n) z.val.1.property
      (by norm_num) z.val.1.property.2).symm

def leftData (z : tube n) : Space n :=
  concat (prefixPath z) (H1ShortArc.arc (endpoint z.val) (point z.val.2))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)

def rightData (z : tube n) : Space n :=
  concat (H1ShortArc.arc (point z.val.2) (endpoint z.val)) (suffixPath z)
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)

theorem leftData_mem (z : tube n) : leftData z ∈ SpherePath n :=
  concat_mem _ _ (by norm_num) (by norm_num) (prefix_mem z)
    (H1ShortArc.arc_mem (backward z)).1 (left_match z)

theorem rightData_mem (z : tube n) : rightData z ∈ SpherePath n :=
  concat_mem _ _ (by norm_num) (by norm_num) (H1ShortArc.arc_mem (forward z)).1
    (suffix_mem z) (right_match z)

theorem leftData_zero (z : tube n) :
    continuousRepresentative (leftData z) 0 = basepoint z.val.2 :=
  (representative_concat_zero _ _ (by norm_num) (by norm_num)).trans
    (representative_restrict_zero _ (by norm_num) z.val.1.property z.val.1.property.1)

theorem leftData_one (z : tube n) :
    continuousRepresentative (leftData z) 1 = basepoint z.val.2 :=
  (representative_concat_one _ _ (by norm_num) (by norm_num) (left_match z)).trans
    (H1ShortArc.arc_mem (backward z)).2.2

theorem rightData_zero (z : tube n) :
    continuousRepresentative (rightData z) 0 = basepoint z.val.2 :=
  (representative_concat_zero _ _ (by norm_num) (by norm_num)).trans
    (H1ShortArc.arc_mem (forward z)).2.1

theorem rightData_one (z : tube n) :
    continuousRepresentative (rightData z) 1 = basepoint z.val.2 :=
  (representative_concat_one _ _ (by norm_num) (by norm_num) (right_match z)).trans
    ((representative_restrict_one _ z.val.1.property (by norm_num)
      z.val.1.property.2).trans (periodic_trace z.val.2))

def left (z : tube n) : SphereLoop n :=
  ⟨⟨leftData z, (mem_periodicSubmodule_iff _).mpr
    ((leftData_one z).trans (leftData_zero z).symm)⟩,
    fun t => leftData_mem z t t.property⟩

def right (z : tube n) : SphereLoop n :=
  ⟨⟨rightData z, (mem_periodicSubmodule_iff _).mpr
    ((rightData_one z).trans (rightData_zero z).symm)⟩,
    fun t => rightData_mem z t t.property⟩

theorem continuous_leftData : Continuous (leftData (n := n)) := by
  have hp := (continuous_prefix (n := n)).prodMk
    (H1ShortArc.continuous_arc.comp (continuous_backward (n := n)))
  have hm : Continuous (fun z : tube n => (⟨(prefixPath z,
      H1ShortArc.arc (endpoint z.val) (point z.val.2)),
        show (prefixPath z, H1ShortArc.arc (endpoint z.val) (point z.val.2)) ∈ matching n from
          sub_eq_zero.mpr (left_match z)⟩ : matching n)) := hp.subtype_mk _
  exact ((continuous_concatenation (n := n) (1/2) (by norm_num) (by norm_num)).comp hm).congr
    (fun z => rfl)

theorem continuous_rightData : Continuous (rightData (n := n)) := by
  have hp := (H1ShortArc.continuous_arc.comp (continuous_forward (n := n))).prodMk
    (continuous_suffix (n := n))
  have hm : Continuous (fun z : tube n => (⟨(H1ShortArc.arc
      (point z.val.2) (endpoint z.val), suffixPath z),
        show (H1ShortArc.arc (point z.val.2) (endpoint z.val), suffixPath z) ∈ matching n from
          sub_eq_zero.mpr (right_match z)⟩ : matching n)) := hp.subtype_mk _
  exact ((continuous_concatenation (n := n) (1/2) (by norm_num) (by norm_num)).comp hm).congr
    (fun z => rfl)

theorem continuous_left : Continuous (left (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact sphereLoop_tendsto_iff.mpr continuous_leftData.continuousAt

theorem continuous_right : Continuous (right (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact sphereLoop_tendsto_iff.mpr continuous_rightData.continuousAt

theorem basepoint_left (z : tube n) : basepoint (left z) = basepoint z.val.2 := leftData_zero z

theorem basepoint_right (z : tube n) : basepoint (right z) = basepoint z.val.2 := rightData_zero z

theorem length_left (F : ReversibleMetric n) (z : tube n) :
    SobolevLength.length F (left z) = H1PathLength.length F (prefixPath z) +
      H1PathLength.length F (H1ShortArc.arc (endpoint z.val) (point z.val.2)) :=
  H1PathLength.length_concat F _ _ (by norm_num) (by norm_num) (prefix_mem z)
    (H1ShortArc.arc_mem (backward z)).1 (left_match z)

theorem length_right (F : ReversibleMetric n) (z : tube n) :
    SobolevLength.length F (right z) =
      H1PathLength.length F (H1ShortArc.arc (point z.val.2) (endpoint z.val)) +
        H1PathLength.length F (suffixPath z) :=
  H1PathLength.length_concat F _ _ (by norm_num) (by norm_num)
    (H1ShortArc.arc_mem (forward z)).1 (suffix_mem z) (right_match z)

theorem length_sum (F : ReversibleMetric n) (z : tube n) :
    SobolevLength.length F (left z) + SobolevLength.length F (right z) =
      SobolevLength.length F z.val.2 +
        H1PathLength.length F (H1ShortArc.arc (endpoint z.val) (point z.val.2)) +
          H1PathLength.length F (H1ShortArc.arc (point z.val.2) (endpoint z.val)) := by
  rw [length_left, length_right]
  have h := H1PathLength.length_restrictions_add F (sphereLoop_mem z.val.2) z.val.1
  change H1PathLength.length F (prefixPath z) + H1PathLength.length F (suffixPath z) =
    SobolevLength.length F z.val.2 at h
  linarith

theorem exists_length_control (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z : tube n,
      ‖(endpoint z.val : Ambient n) - (point z.val.2 : Ambient n)‖ < ρ →
        SobolevLength.length F (left z) + SobolevLength.length F (right z) <
          SobolevLength.length F z.val.2 + 2 * ε := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := H1ShortArc.exists_length_radius F hε
  refine ⟨ρ, hρ, hρ1, fun z hz => ?_⟩
  have h1 := hb (forward z) hz
  have h2 := hb (backward z) (by
    change ‖(point z.val.2 : Ambient n) - (endpoint z.val : Ambient n)‖ < ρ
    rwa [norm_sub_rev])
  rw [length_sum]
  change H1PathLength.length F (H1ShortArc.arc (point z.val.2) (endpoint z.val)) < ε at h1
  change H1PathLength.length F (H1ShortArc.arc (endpoint z.val) (point z.val.2)) < ε at h2
  linarith

end
end Finsler.H1SelfCutNeighborhood
