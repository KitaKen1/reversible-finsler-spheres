module

public import Finsler.Loop.OrderedDoubleCutTimes
public import Finsler.Topology.SupportedSelfCut

/-! A COMMON genuine ordered two-time near-domain for the original
H1 loop. Three actual based closed loops are constructed directly:
the original first prefix cut, arc--middle restriction--arc, and the
original last suffix cut. No sequential-cap comparison is assumed. -/
@[expose] public section
namespace Finsler.NativeOrderedDoubleCutGeometry
open CategoryTheory MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1SelfCutNeighborhood Finsler.H1AffineRestrictionContinuity Finsler.H1ConcatContinuity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

abbrev source (n : ℕ) := TopCat.of (SphereLoop n × OrderedDoubleCutTimes.space)

def firstParameter (n : ℕ) : source n ⟶ SelfCutThomCocycle.parameters n := TopCat.ofHom
  ⟨fun z => (z.2.val.1.down, z.1), by fun_prop⟩

def lastParameter (n : ℕ) : source n ⟶ SelfCutThomCocycle.parameters n := TopCat.ofHom
  ⟨fun z => (z.2.val.2.down, z.1), by fun_prop⟩

def near (n : ℕ) (r : ℝ) : Set (source n) := {z |
  SupportedSelfCut.distance n (firstParameter n z) < r ∧
    SupportedSelfCut.distance n (lastParameter n z) < r}

abbrev domain (n : ℕ) (r : ℝ) := TopCat.of (near n r)

variable {n : ℕ} {r : ℝ}

def firstCut (hr : r ≤ 1) (z : domain n r) : tube n :=
  ⟨firstParameter n z.val, z.property.1.trans_le hr⟩

def lastCut (hr : r ≤ 1) (z : domain n r) : tube n :=
  ⟨lastParameter n z.val, z.property.2.trans_le hr⟩

theorem continuous_firstCut (hr : r ≤ 1) : Continuous (firstCut (n := n) hr) :=
  ((firstParameter n).hom.continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_lastCut (hr : r ≤ 1) : Continuous (lastCut (n := n) hr) :=
  ((lastParameter n).hom.continuous.comp continuous_subtype_val).subtype_mk _

def rawMiddle (z : domain n r) : Space n :=
  restrict (z.val.1.data : Space n) z.val.2.val.1.down.property z.val.2.val.2.down.property z.val.2.property

theorem rawMiddle_mem (z : domain n r) : rawMiddle z ∈ SpherePath n :=
  restrict_mem (sphereLoop_mem z.val.1) _ _ _

theorem continuous_rawMiddle : Continuous (rawMiddle (n := n) (r := r)) := by
  have hu : Continuous (fun z : domain n r => (z.val.1.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp (continuous_fst.comp continuous_subtype_val)
  have hi : Continuous (fun z : domain n r =>
      (⟨(z.val.2.val.1.down, z.val.2.val.2.down), z.val.2.property⟩ : Intervals)) := by
    fun_prop
  exact (continuous_restriction (n := n)).comp (hi.prodMk hu)

def firstArc (hr : r ≤ 1) (z : domain n r) : Space n :=
  H1ShortArc.arc (point z.val.1) (endpoint (firstCut hr z).val)

def lastArc (hr : r ≤ 1) (z : domain n r) : Space n :=
  H1ShortArc.arc (endpoint (lastCut hr z).val) (point z.val.1)

theorem firstArc_mem (hr : r ≤ 1) (z : domain n r) : firstArc hr z ∈ SpherePath n :=
  (H1ShortArc.arc_mem (forward (firstCut hr z))).1

theorem lastArc_mem (hr : r ≤ 1) (z : domain n r) : lastArc hr z ∈ SpherePath n :=
  (H1ShortArc.arc_mem (backward (lastCut hr z))).1

theorem continuous_firstArc (hr : r ≤ 1) : Continuous (firstArc (n := n) hr) :=
  ((H1ShortArc.continuous_arc (n := n)).comp
    ((continuous_forward (n := n)).comp (continuous_firstCut hr))).congr (fun _ => rfl)

theorem continuous_lastArc (hr : r ≤ 1) : Continuous (lastArc (n := n) hr) :=
  ((H1ShortArc.continuous_arc (n := n)).comp
    ((continuous_backward (n := n)).comp (continuous_lastCut hr))).congr (fun _ => rfl)

theorem middle_last_match (hr : r ≤ 1) (z : domain n r) : continuousRepresentative (rawMiddle z) 1 =
    continuousRepresentative (lastArc hr z) 0 :=
  (representative_restrict_one _ _ _ _).trans (H1ShortArc.arc_mem (backward (lastCut hr z))).2.1.symm

def tail (hr : r ≤ 1) (z : domain n r) : Space n := concat (rawMiddle z) (lastArc hr z)
  (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)

theorem tail_mem (hr : r ≤ 1) (z : domain n r) : tail hr z ∈ SpherePath n :=
  concat_mem _ _ (by norm_num) (by norm_num) (rawMiddle_mem z) (lastArc_mem hr z) (middle_last_match hr z)

theorem first_tail_match (hr : r ≤ 1) (z : domain n r) : continuousRepresentative (firstArc hr z) 1 =
    continuousRepresentative (tail hr z) 0 :=
  (H1ShortArc.arc_mem (forward (firstCut hr z))).2.2.trans
    ((representative_restrict_zero _ _ _ _).symm.trans (representative_concat_zero _ _ (by norm_num) (by norm_num)).symm)

def middleData (hr : r ≤ 1) (z : domain n r) : Space n := concat (firstArc hr z) (tail hr z)
  (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)

theorem middleData_mem (hr : r ≤ 1) (z : domain n r) : middleData hr z ∈ SpherePath n :=
  concat_mem _ _ (by norm_num) (by norm_num) (firstArc_mem hr z) (tail_mem hr z) (first_tail_match hr z)

theorem middle_zero (hr : r ≤ 1) (z : domain n r) : continuousRepresentative (middleData hr z) 0 = (point z.val.1 : Ambient n) :=
  (representative_concat_zero _ _ (by norm_num) (by norm_num)).trans
    (H1ShortArc.arc_mem (forward (firstCut hr z))).2.1

theorem middle_one (hr : r ≤ 1) (z : domain n r) : continuousRepresentative (middleData hr z) 1 = (point z.val.1 : Ambient n) :=
  (representative_concat_one _ _ (by norm_num) (by norm_num) (first_tail_match hr z)).trans
    ((representative_concat_one _ _ (by norm_num) (by norm_num) (middle_last_match hr z)).trans
      (H1ShortArc.arc_mem (backward (lastCut hr z))).2.2)

def middle (hr : r ≤ 1) (z : domain n r) : SphereLoop n :=
  ⟨⟨middleData hr z, (mem_periodicSubmodule_iff _).mpr ((middle_one hr z).trans (middle_zero hr z).symm)⟩,
    fun t => middleData_mem hr z t t.property⟩

theorem continuous_tail (hr : r ≤ 1) : Continuous (tail (n := n) hr) := by
  have h : Continuous (fun z : domain n r => (⟨(rawMiddle z, lastArc hr z),
      show (rawMiddle z, lastArc hr z) ∈ matching n from sub_eq_zero.mpr (middle_last_match hr z)⟩ : matching n)) :=
    (continuous_rawMiddle.prodMk (continuous_lastArc hr)).subtype_mk _
  exact ((continuous_concatenation (n := n) (1 / 2) (by norm_num) (by norm_num)).comp h).congr
    (fun _ => rfl)

theorem continuous_middleData (hr : r ≤ 1) : Continuous (middleData (n := n) hr) := by
  have h : Continuous (fun z : domain n r => (⟨(firstArc hr z, tail hr z),
      show (firstArc hr z, tail hr z) ∈ matching n from sub_eq_zero.mpr (first_tail_match hr z)⟩ : matching n)) :=
    ((continuous_firstArc hr).prodMk (continuous_tail hr)).subtype_mk _
  exact ((continuous_concatenation (n := n) (1 / 2) (by norm_num) (by norm_num)).comp h).congr
    (fun _ => rfl)

theorem continuous_middle (hr : r ≤ 1) : Continuous (middle (n := n) hr) :=
  continuous_iff_continuousAt.mpr (fun _ => sphereLoop_tendsto_iff.mpr (continuous_middleData hr).continuousAt)

theorem middle_length (hr : r ≤ 1) (F : ReversibleMetric n) (z : domain n r) :
    SobolevLength.length F (middle hr z) =
      H1PathLength.length F (firstArc hr z) + H1PathLength.length F (rawMiddle z) +
        H1PathLength.length F (lastArc hr z) := by
  change H1PathLength.length F (middleData hr z) = _
  rw [middleData, H1PathLength.length_concat F _ _ (by norm_num) (by norm_num)
    (firstArc_mem hr z) (tail_mem hr z) (first_tail_match hr z),
    tail, H1PathLength.length_concat F _ _ (by norm_num) (by norm_num)
      (rawMiddle_mem z) (lastArc_mem hr z) (middle_last_match hr z)]
  ring

end
end Finsler.NativeOrderedDoubleCutGeometry
