module

public import Finsler.Loop.NativeSequentialSupportedStages

/-! Both clock maps on the WHOLE original raw source, including all
endpoints. Exact parameter squares identify the original outer/inner
Thom cochains and near/far geometry with the common ordered source.
No full sequential-time or high-power UNIT conclusion is asserted. -/
@[expose] public section
namespace Finsler.NativeRawClockMaps
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeSelfCutSegmentClocks
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

def prefixClock (n : ℕ) : source n ⟶ NativeOrderedDoubleCutGeometry.source n := TopCat.ofHom
  ⟨fun z => (z.1.2, OrderedDoubleCutTimes.leftClock (ULift.up z.1.1, ULift.up z.2)), by
    exact continuous_fst.snd.prodMk (OrderedDoubleCutTimes.leftClock.hom.continuous.comp
      ((continuous_uliftUp.comp continuous_fst.fst).prodMk (continuous_uliftUp.comp continuous_snd)))⟩

def suffixClock (n : ℕ) : source n ⟶ NativeOrderedDoubleCutGeometry.source n := TopCat.ofHom
  ⟨fun z => (z.1.2, OrderedDoubleCutTimes.rightClock (ULift.up z.1.1, ULift.up z.2)), by
    exact continuous_fst.snd.prodMk (OrderedDoubleCutTimes.rightClock.hom.continuous.comp
      ((continuous_uliftUp.comp continuous_fst.fst).prodMk (continuous_uliftUp.comp continuous_snd)))⟩

theorem prefix_outer (n : ℕ) : prefixClock n ≫ NativeOrderedDoubleCutGeometry.lastParameter n =
    firstParameter n := rfl

theorem suffix_outer (n : ℕ) : suffixClock n ≫ NativeOrderedDoubleCutGeometry.firstParameter n =
    firstParameter n := rfl

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def outerInclusion : outerSpace m hm F ⟶ source (m + 1) :=
  SupportedCap.subspaceMap (source (m + 1))
    (NativeOrderedDoubleCutSupported.near (firstParameter (m + 1)) (radius m hm F))

theorem prefix_inner : outerInclusion m hm F ≫ prefixClock (m + 1) ≫
    NativeOrderedDoubleCutGeometry.firstParameter (m + 1) =
    outer m hm F ≫ NativeSequentialCutParameters.prefixOriginal (m + 1) := rfl

theorem suffix_inner : outerInclusion m hm F ≫ suffixClock (m + 1) ≫
    NativeOrderedDoubleCutGeometry.lastParameter (m + 1) =
    outer m hm F ≫ NativeSequentialCutParameters.suffixOriginal (m + 1) := rfl

theorem prefix_inner_distance (z : outerSpace m hm F) :
    SupportedSelfCut.distance (m + 1)
      (NativeOrderedDoubleCutGeometry.firstParameter (m + 1) (prefixClock (m + 1) (outerInclusion m hm F z))) =
    SupportedSelfCut.distance (m + 1) (prefixParameter m hm F z) :=
  (NativeSequentialCutParameters.prefix_distance (outer m hm F z)).symm

theorem suffix_inner_distance (z : outerSpace m hm F) :
    SupportedSelfCut.distance (m + 1)
      (NativeOrderedDoubleCutGeometry.lastParameter (m + 1) (suffixClock (m + 1) (outerInclusion m hm F z))) =
    SupportedSelfCut.distance (m + 1) (suffixParameter m hm F z) :=
  (NativeSequentialCutParameters.suffix_distance (outer m hm F z)).symm

theorem prefix_inner_thom :
    cochainPullback (outerInclusion m hm F ≫ prefixClock (m + 1)) (m + 1)
      (NativeOrderedDoubleCutSupported.thom (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
        (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) =
    NativeOrderedDoubleCutSupported.thom (prefixParameter m hm F) (by omega)
      (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) := by
  unfold NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  exact (prefix_thom_original_clock m hm F).symm

theorem suffix_inner_thom :
    cochainPullback (outerInclusion m hm F ≫ suffixClock (m + 1)) (m + 1)
      (NativeOrderedDoubleCutSupported.thom (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
        (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) =
    NativeOrderedDoubleCutSupported.thom (suffixParameter m hm F) (by omega)
      (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) := by
  unfold NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  exact (suffix_thom_original_clock m hm F).symm

theorem prefix_inner_near (r : ℝ) :
    (outerInclusion m hm F ≫ prefixClock (m + 1)) ⁻¹'
      NativeOrderedDoubleCutSupported.near (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) r =
    NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) r := by
  ext z
  change SupportedSelfCut.distance (m + 1) _ < r ↔ SupportedSelfCut.distance (m + 1) _ < r
  exact (congrArg (fun v : ℝ => v < r) (prefix_inner_distance m hm F z)).to_iff

theorem suffix_inner_near (r : ℝ) :
    (outerInclusion m hm F ≫ suffixClock (m + 1)) ⁻¹'
      NativeOrderedDoubleCutSupported.near (NativeOrderedDoubleCutGeometry.lastParameter (m + 1)) r =
    NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) r := by
  ext z
  change SupportedSelfCut.distance (m + 1) _ < r ↔ SupportedSelfCut.distance (m + 1) _ < r
  exact (congrArg (fun v : ℝ => v < r) (suffix_inner_distance m hm F z)).to_iff

theorem prefix_inner_far (ρ : ℝ) :
    (outerInclusion m hm F ≫ prefixClock (m + 1)) ⁻¹'
      NativeOrderedDoubleCutSupported.far (NativeOrderedDoubleCutGeometry.firstParameter (m + 1)) ρ =
    NativeOrderedDoubleCutSupported.far (prefixParameter m hm F) ρ := by
  ext z
  change ρ < SupportedSelfCut.distance (m + 1) _ ↔ ρ < SupportedSelfCut.distance (m + 1) _
  exact (congrArg (fun v : ℝ => ρ < v) (prefix_inner_distance m hm F z)).to_iff

theorem suffix_inner_far (ρ : ℝ) :
    (outerInclusion m hm F ≫ suffixClock (m + 1)) ⁻¹'
      NativeOrderedDoubleCutSupported.far (NativeOrderedDoubleCutGeometry.lastParameter (m + 1)) ρ =
    NativeOrderedDoubleCutSupported.far (suffixParameter m hm F) ρ := by
  ext z
  change ρ < SupportedSelfCut.distance (m + 1) _ ↔ ρ < SupportedSelfCut.distance (m + 1) _
  exact (congrArg (fun v : ℝ => ρ < v) (suffix_inner_distance m hm F z)).to_iff

end
end Finsler.NativeRawClockMaps
