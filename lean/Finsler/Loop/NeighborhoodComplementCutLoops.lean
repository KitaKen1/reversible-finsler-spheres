module

public import Finsler.Loop.WholeSelfCutComplement
public import Finsler.Loop.H1PathRepresentativeCalculus
public import Finsler.Topology.JoinSplitHomotopy

/-! On the WHOLE original near-diagonal tube, complementary cut loops
are literal half-period rotations of the original opposite outputs.
This includes unequal endpoints and BOTH endpoint times. All equalities
are of the original strong-H1 graph loops; no coincidence restriction.
Consequently their actual ordinary cohomology pullbacks agree. -/
@[expose] public section
namespace Finsler.NeighborhoodComplementCutLoops
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevAffine
open Finsler.SobolevSpherePath
open Finsler.SobolevConcat Finsler.SobolevShift Finsler.SobolevCircleRepresentative
open Finsler.NativeTripleSelfEvaluation Finsler.CompactH1Alignment Finsler.SobolevEnergy
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000
local notation "I" => ClosedInterval

def tubeComplement {n : ℕ} (z : tube n) : tube n :=
  ⟨WholeSelfCutComplement.complement n z.val, by
    change SupportedSelfCut.distance n (WholeSelfCutComplement.complement n z.val) < 1
    rw [WholeSelfCutComplement.distance_complement]
    exact z.property⟩

theorem continuous_tubeComplement (n : ℕ) : Continuous (tubeComplement (n := n)) :=
  ((WholeSelfCutComplement.complement n).hom.continuous.comp continuous_subtype_val).subtype_mk _

def tubeMap (n : ℕ) : TopCat.of (tube n) ⟶ TopCat.of (tube n) :=
  TopCat.ofHom ⟨tubeComplement, continuous_tubeComplement n⟩

theorem prefix_point {n : ℕ} (z : SelfCutThomCocycle.parameters n) (s : I) :
    sphereRepresentative (WholeSelfCutComplement.complement n z).2
      (DiagonalSelfCutRepresentatives.prefixTime (WholeSelfCutComplement.complement n z).1 s) =
    sphereRepresentative z.2 (DiagonalSelfCutRepresentatives.suffixTime z.1 s) := by
  change sphereRepresentative (shiftSphere z.2 (z.1 : ℝ))
    (DiagonalSelfCutRepresentatives.prefixTime (unitInterval.symm z.1) s) = _
  rw [endpoint_shift]
  have ha : ((z.1 : ℝ) : SobolevCircleRepresentative.Circle) +
      ((DiagonalSelfCutRepresentatives.prefixTime (unitInterval.symm z.1) s : ℝ) : SobolevCircleRepresentative.Circle) =
      ((DiagonalSelfCutRepresentatives.suffixTime z.1 s : ℝ) : SobolevCircleRepresentative.Circle) := by
    rw [← AddCircle.coe_add]
    congr 1
  rw [ha, sphereCircleMap_coe]

theorem suffix_point {n : ℕ} (z : SelfCutThomCocycle.parameters n) (s : I) :
    sphereRepresentative (WholeSelfCutComplement.complement n z).2
      (DiagonalSelfCutRepresentatives.suffixTime (WholeSelfCutComplement.complement n z).1 s) =
    sphereRepresentative z.2 (DiagonalSelfCutRepresentatives.prefixTime z.1 s) := by
  change sphereRepresentative (shiftSphere z.2 (z.1 : ℝ))
    (DiagonalSelfCutRepresentatives.suffixTime (unitInterval.symm z.1) s) = _
  rw [endpoint_shift]
  have ha : ((z.1 : ℝ) : SobolevCircleRepresentative.Circle) +
      ((DiagonalSelfCutRepresentatives.suffixTime (unitInterval.symm z.1) s : ℝ) : SobolevCircleRepresentative.Circle) =
      ((DiagonalSelfCutRepresentatives.prefixTime z.1 s : ℝ) : SobolevCircleRepresentative.Circle) := by
    rw [← AddCircle.coe_add]
    have he : (z.1 : ℝ) + (DiagonalSelfCutRepresentatives.suffixTime (unitInterval.symm z.1) s : ℝ) =
        (DiagonalSelfCutRepresentatives.prefixTime z.1 s : ℝ) + 1 := by
      change (z.1 : ℝ) + ((1 - (z.1 : ℝ)) + (1 - (1 - (z.1 : ℝ))) * s) = (z.1 : ℝ) * s + 1
      ring
    rw [he, AddCircle.coe_add_period]
  rw [ha, sphereCircleMap_coe]

theorem prefix_complement {n : ℕ} (z : tube n) : prefixPath (tubeComplement z) = suffixPath z := by
  apply eq_of_representative_eqOn
  intro s hs
  rw [prefixPath, suffixPath, representative_restrict _ (by norm_num)
    (tubeComplement z).val.1.property (tubeComplement z).val.1.property.1 hs,
    representative_restrict _ z.val.1.property (by norm_num) z.val.1.property.2 hs]
  have he := congrArg Subtype.val (prefix_point z.val ⟨s, hs⟩)
  change continuousRepresentative ((WholeSelfCutComplement.complement n z.val).2.data : Space n)
      ((1 - (z.val.1 : ℝ)) * s) =
    continuousRepresentative (z.val.2.data : Space n) (aff z.val.1 1 s) at he
  change continuousRepresentative ((WholeSelfCutComplement.complement n z.val).2.data : Space n)
    (0 + ((1 - (z.val.1 : ℝ)) - 0) * s) =
    continuousRepresentative (z.val.2.data : Space n) (aff z.val.1 1 s)
  simpa only [aff, sub_zero, zero_add] using he

theorem suffix_complement {n : ℕ} (z : tube n) : suffixPath (tubeComplement z) = prefixPath z := by
  apply eq_of_representative_eqOn
  intro s hs
  rw [suffixPath, prefixPath, representative_restrict _ (tubeComplement z).val.1.property
    (by norm_num) (tubeComplement z).val.1.property.2 hs,
    representative_restrict _ (by norm_num) z.val.1.property z.val.1.property.1 hs]
  have he := congrArg Subtype.val (suffix_point z.val ⟨s, hs⟩)
  change continuousRepresentative ((WholeSelfCutComplement.complement n z.val).2.data : Space n)
      (aff (unitInterval.symm z.val.1) 1 s) =
    continuousRepresentative (z.val.2.data : Space n) ((z.val.1 : ℝ) * s) at he
  change continuousRepresentative ((WholeSelfCutComplement.complement n z.val).2.data : Space n)
    (aff (unitInterval.symm z.val.1) 1 s) =
    continuousRepresentative (z.val.2.data : Space n) (aff 0 z.val.1 s)
  simpa only [aff, sub_zero, zero_add] using he

theorem left_data_complement {n : ℕ} (z : tube n) :
    leftData (tubeComplement z) =
      concat (suffixPath z) (H1ShortArc.arc (point z.val.2) (endpoint z.val)) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) := by
  unfold leftData
  rw [prefix_complement]
  change concat (suffixPath z)
    (H1ShortArc.arc (endpoint (WholeSelfCutComplement.complement n z.val))
      (point (WholeSelfCutComplement.complement n z.val).2)) _ _ = _
  rw [WholeSelfCutComplement.endpoint_complement, WholeSelfCutComplement.point_complement]

theorem right_data_complement {n : ℕ} (z : tube n) :
    rightData (tubeComplement z) =
      concat (H1ShortArc.arc (endpoint z.val) (point z.val.2)) (prefixPath z) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) := by
  unfold rightData
  rw [suffix_complement]
  change concat (H1ShortArc.arc (point (WholeSelfCutComplement.complement n z.val).2)
    (endpoint (WholeSelfCutComplement.complement n z.val))) (prefixPath z) _ _ = _
  rw [WholeSelfCutComplement.endpoint_complement, WholeSelfCutComplement.point_complement]

private theorem half_concat_swap {n : ℕ} (u v : Space n) (w w' : SphereLoop n)
    (hw : (w.data : Space n) = concat u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num))
    (hw' : (w'.data : Space n) = concat v u (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num))
    (hm : continuousRepresentative u 1 = continuousRepresentative v 0)
    (hm' : continuousRepresentative v 1 = continuousRepresentative u 0) :
    shiftSphere w (1 / 2) = w' := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (shiftData w.data (1 / 2)) t = continuousRepresentative (w'.data : Space n) t
  rw [hw', representative_shiftData w.data (1 / 2) t.property]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [realMap_eqOn w.data ⟨by linarith [t.property.1], by linarith⟩, hw,
      representative_concat_right u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) hm
        ⟨by linarith [t.property.1], by linarith⟩,
      representative_concat_left v u (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) ⟨t.property.1, ht⟩]
    congr 1
    norm_num [rightMap]
    ring
  · have he : (t : ℝ) + 1 / 2 = ((t : ℝ) - 1 / 2) + 1 := by ring
    rw [he, realMap_periodic w.data,
      realMap_eqOn w.data ⟨by linarith, by linarith [t.property.2]⟩, hw,
      representative_concat_left u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) ⟨by linarith, by linarith [t.property.2]⟩,
      representative_concat_right v u (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) hm' ⟨by linarith, t.property.2⟩]
    congr 1
    norm_num [rightMap]
    ring

theorem retained_half_shift {n : ℕ} (z : tube n) :
    shiftSphere (right z) (1 / 2) = left (tubeComplement z) := by
  apply half_concat_swap (H1ShortArc.arc (point z.val.2) (endpoint z.val)) (suffixPath z)
    (right z) (left (tubeComplement z)) rfl (left_data_complement z) (right_match z)
  have hm := left_match (tubeComplement z)
  rw [prefix_complement] at hm
  change continuousRepresentative (suffixPath z) 1 =
    continuousRepresentative (H1ShortArc.arc (endpoint (WholeSelfCutComplement.complement n z.val))
      (point (WholeSelfCutComplement.complement n z.val).2)) 0 at hm
  rwa [WholeSelfCutComplement.endpoint_complement, WholeSelfCutComplement.point_complement] at hm

theorem tested_half_shift {n : ℕ} (z : tube n) :
    shiftSphere (left z) (1 / 2) = right (tubeComplement z) := by
  apply half_concat_swap (prefixPath z) (H1ShortArc.arc (endpoint z.val) (point z.val.2))
    (left z) (right (tubeComplement z)) rfl (right_data_complement z) (left_match z)
  have hm := right_match (tubeComplement z)
  rw [suffix_complement] at hm
  change continuousRepresentative (H1ShortArc.arc (point (WholeSelfCutComplement.complement n z.val).2)
      (endpoint (WholeSelfCutComplement.complement n z.val))) 1 =
    continuousRepresentative (prefixPath z) 0 at hm
  rwa [WholeSelfCutComplement.endpoint_complement, WholeSelfCutComplement.point_complement] at hm

def testedOrdinary (n : ℕ) : TopCat.of (tube n) ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap (left z), (sphereCircleMap_continuous n).comp continuous_left⟩
def retainedOrdinary (n : ℕ) : TopCat.of (tube n) ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap (right z), (sphereCircleMap_continuous n).comp continuous_right⟩

def retainedRotationHomotopy (n : ℕ) :
    TopCat.Homotopy (retainedOrdinary n) (tubeMap n ≫ testedOrdinary n) where
  toFun z := OrdinaryLoopRotation.rotate n (((z.1 : ℝ) / 2 : ℝ) : SobolevCircleRepresentative.Circle)
    (retainedOrdinary n z.2)
  continuous_toFun := by
    have ht : Continuous (fun z : _root_.unitInterval × tube n =>
        (((z.1 : ℝ) / 2 : ℝ) : SobolevCircleRepresentative.Circle)) := by fun_prop
    exact (OrdinaryLoopRotation.joint_continuous n).comp
      (((retainedOrdinary n).hom.continuous.comp continuous_snd).prodMk ht)
  map_zero_left z := by
    change OrdinaryLoopRotation.rotate n (((0 : ℝ) / 2 : ℝ) : SobolevCircleRepresentative.Circle) _ = _
    rw [zero_div, AddCircle.coe_zero, OrdinaryLoopRotation.rotate_zero]
  map_one_left z := by
    have he := congrArg sphereCircleMap (retained_half_shift z)
    rw [circleMap_shiftSphere] at he
    exact he

def testedRotationHomotopy (n : ℕ) :
    TopCat.Homotopy (testedOrdinary n) (tubeMap n ≫ retainedOrdinary n) where
  toFun z := OrdinaryLoopRotation.rotate n (((z.1 : ℝ) / 2 : ℝ) : SobolevCircleRepresentative.Circle)
    (testedOrdinary n z.2)
  continuous_toFun := by
    have ht : Continuous (fun z : _root_.unitInterval × tube n =>
        (((z.1 : ℝ) / 2 : ℝ) : SobolevCircleRepresentative.Circle)) := by fun_prop
    exact (OrdinaryLoopRotation.joint_continuous n).comp
      (((testedOrdinary n).hom.continuous.comp continuous_snd).prodMk ht)
  map_zero_left z := by
    change OrdinaryLoopRotation.rotate n (((0 : ℝ) / 2 : ℝ) : SobolevCircleRepresentative.Circle) _ = _
    rw [zero_div, AddCircle.coe_zero, OrdinaryLoopRotation.rotate_zero]
  map_one_left z := by
    have he := congrArg sphereCircleMap (tested_half_shift z)
    rw [circleMap_shiftSphere] at he
    exact he

theorem tested_cohomology_swap (n q : ℕ) (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (tubeMap n ≫ testedOrdinary n) q).hom a = (cohPullback (retainedOrdinary n) q).hom a :=
  (LoopSweepTwoPiece.cohomology_homotopy (retainedRotationHomotopy n) q a).symm

theorem retained_cohomology_swap (n q : ℕ) (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (tubeMap n ≫ retainedOrdinary n) q).hom a = (cohPullback (testedOrdinary n) q).hom a :=
  (LoopSweepTwoPiece.cohomology_homotopy (testedRotationHomotopy n) q a).symm

end
end Finsler.NeighborhoodComplementCutLoops
