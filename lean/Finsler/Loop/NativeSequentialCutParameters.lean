module

public import Finsler.Loop.NativeSelfCutSegmentClocks
public import Finsler.Loop.NativeOrderedDoubleCutGeometry
public import Finsler.Topology.NormalizedSelfCut

/-! Both ORIGINAL sequential cut branches on their actual raw path
halves. The basepoint and endpoint evaluation diagrams, original Thom
cochains and distances agree EXACTLY with the original-loop clocks.
Inner-tube membership follows from those original near conditions;
it is not an independent assumption. Endpoints and seams are included. -/
@[expose] public section
namespace Finsler.NativeSequentialCutParameters
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.H1SelfCutNeighborhood Finsler.NativeSelfCutSegmentClocks
open Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

abbrev source (n : ℕ) := TopCat.of (tube n × ClosedInterval)

def prefixOriginal (n : ℕ) : source n ⟶ SelfCutThomCocycle.parameters n := TopCat.ofHom
  ⟨fun z => (prefixTime z.1.val.1 z.2, z.1.val.2),
    (continuous_prefixTime.comp ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_snd)).prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))⟩

def suffixOriginal (n : ℕ) : source n ⟶ SelfCutThomCocycle.parameters n := TopCat.ofHom
  ⟨fun z => (suffixTime z.1.val.1 z.2, z.1.val.2),
    (continuous_suffixTime.comp ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_snd)).prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))⟩

def prefixParameter (n : ℕ) : source n ⟶ SelfCutThomCocycle.parameters n := TopCat.ofHom
  ⟨fun z => (firstHalf z.2, left z.1),
    (continuous_firstHalf.comp continuous_snd).prodMk ((continuous_left (n := n)).comp continuous_fst)⟩

def suffixParameter (n : ℕ) : source n ⟶ SelfCutThomCocycle.parameters n := TopCat.ofHom
  ⟨fun z => (secondHalf z.2, right z.1),
    (continuous_secondHalf.comp continuous_snd).prodMk ((continuous_right (n := n)).comp continuous_fst)⟩

theorem point_left {n : ℕ} (z : tube n) : point (left z) = point z.val.2 :=
  Subtype.ext (basepoint_left z)

theorem point_right {n : ℕ} (z : tube n) : point (right z) = point z.val.2 :=
  Subtype.ext (basepoint_right z)

theorem prefix_selfEvaluation (n : ℕ) : prefixParameter n ≫ SelfCutThomCocycle.selfEvaluation n =
    prefixOriginal n ≫ SelfCutThomCocycle.selfEvaluation n := by
  apply TopCat.ext
  intro z
  exact Prod.ext (point_left z.1) (left_prefix z.1 z.2)

theorem suffix_selfEvaluation (n : ℕ) : suffixParameter n ≫ SelfCutThomCocycle.selfEvaluation n =
    suffixOriginal n ≫ SelfCutThomCocycle.selfEvaluation n := by
  apply TopCat.ext
  intro z
  exact Prod.ext (point_right z.1) (right_suffix z.1 z.2)

theorem prefix_distance {n : ℕ} (z : source n) :
    SupportedSelfCut.distance n (prefixParameter n z) = SupportedSelfCut.distance n (prefixOriginal n z) := by
  change ‖(sphereRepresentative (left z.1) (firstHalf z.2) : Ambient n) - (point (left z.1) : Ambient n)‖ = _
  rw [left_prefix, point_left]
  rfl

theorem suffix_distance {n : ℕ} (z : source n) :
    SupportedSelfCut.distance n (suffixParameter n z) = SupportedSelfCut.distance n (suffixOriginal n z) := by
  change ‖(sphereRepresentative (right z.1) (secondHalf z.2) : Ambient n) - (point (right z.1) : Ambient n)‖ = _
  rw [right_suffix, point_right]
  rfl

theorem prefix_thom (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (prefixParameter n) n (NormalizedSelfCut.cocycle n hn hρ) =
      cochainPullback (prefixOriginal n) n (NormalizedSelfCut.cocycle n hn hρ) := by
  simp only [NormalizedSelfCut.cocycle, ← pullback_comp, prefix_selfEvaluation]

theorem suffix_thom (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (suffixParameter n) n (NormalizedSelfCut.cocycle n hn hρ) =
      cochainPullback (suffixOriginal n) n (NormalizedSelfCut.cocycle n hn hρ) := by
  simp only [NormalizedSelfCut.cocycle, ← pullback_comp, suffix_selfEvaluation]

def prefixNear (n : ℕ) (r : ℝ) : Set (source n) := {z |
  SupportedSelfCut.distance n z.1.val < r ∧ SupportedSelfCut.distance n (prefixOriginal n z) < r}

def suffixNear (n : ℕ) (r : ℝ) : Set (source n) := {z |
  SupportedSelfCut.distance n z.1.val < r ∧ SupportedSelfCut.distance n (suffixOriginal n z) < r}

abbrev prefixDomain (n : ℕ) (r : ℝ) := TopCat.of (prefixNear n r)
abbrev suffixDomain (n : ℕ) (r : ℝ) := TopCat.of (suffixNear n r)

variable {n : ℕ} {r : ℝ}

def prefixCut (hr : r ≤ 1) (z : prefixDomain n r) : tube n :=
  ⟨prefixOriginal n z.val, z.property.2.trans_le hr⟩

def suffixCut (hr : r ≤ 1) (z : suffixDomain n r) : tube n :=
  ⟨suffixOriginal n z.val, z.property.2.trans_le hr⟩

def prefixInner (hr : r ≤ 1) (z : prefixDomain n r) : tube n :=
  ⟨prefixParameter n z.val, by
    change SupportedSelfCut.distance n (prefixParameter n z.val) < 1
    rw [prefix_distance]
    exact z.property.2.trans_le hr⟩

def suffixInner (hr : r ≤ 1) (z : suffixDomain n r) : tube n :=
  ⟨suffixParameter n z.val, by
    change SupportedSelfCut.distance n (suffixParameter n z.val) < 1
    rw [suffix_distance]
    exact z.property.2.trans_le hr⟩

theorem continuous_prefixCut (hr : r ≤ 1) : Continuous (prefixCut (n := n) hr) :=
  ((prefixOriginal n).hom.continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_suffixCut (hr : r ≤ 1) : Continuous (suffixCut (n := n) hr) :=
  ((suffixOriginal n).hom.continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_prefixInner (hr : r ≤ 1) : Continuous (prefixInner (n := n) hr) :=
  ((prefixParameter n).hom.continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_suffixInner (hr : r ≤ 1) : Continuous (suffixInner (n := n) hr) :=
  ((suffixParameter n).hom.continuous.comp continuous_subtype_val).subtype_mk _

def prefixCommon (z : prefixDomain n r) : NativeOrderedDoubleCutGeometry.domain n r :=
  ⟨(z.val.1.val.2, ⟨(ULift.up (prefixTime z.val.1.val.1 z.val.2), ULift.up z.val.1.val.1), by
    change (z.val.1.val.1 : ℝ) * z.val.2 ≤ (z.val.1.val.1 : ℝ)
    exact mul_le_of_le_one_right z.val.1.val.1.property.1 z.val.2.property.2⟩),
    z.property.2, z.property.1⟩

def suffixCommon (z : suffixDomain n r) : NativeOrderedDoubleCutGeometry.domain n r :=
  ⟨(z.val.1.val.2, ⟨(ULift.up z.val.1.val.1, ULift.up (suffixTime z.val.1.val.1 z.val.2)), by
    change (z.val.1.val.1 : ℝ) ≤ (z.val.1.val.1 : ℝ) + (1 - z.val.1.val.1) * z.val.2
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr z.val.1.val.1.property.2) z.val.2.property.1)⟩),
    z.property.1, z.property.2⟩

theorem continuous_prefixCommon : Continuous (prefixCommon (n := n) (r := r)) := by
  unfold prefixCommon prefixTime
  fun_prop

theorem continuous_suffixCommon : Continuous (suffixCommon (n := n) (r := r)) := by
  unfold suffixCommon suffixTime
  fun_prop

end
end Finsler.NativeSequentialCutParameters
