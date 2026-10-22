module

public import Finsler.Loop.NativeRawClockDoubleGeometry
public import Finsler.Loop.NativeOrderedScalarPullback

/-! Actual reindexing of each raw far cover into the SAME ordered
cover, and exact pullback identities for BOTH normalized Thom factors
and the SAME local GH test. Prefix reverses the cup order; suffix does
not. No equality of selected full subdivision retractions is assumed. -/
@[expose] public section
namespace Finsler.NativeRawOrderedCupGeometry
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockDoubleGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

abbrev prefixFarFamily := DoubleFarCupOneCap.far (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
abbrev prefixNearSet := outerNear m hm F ∩ prefixNear m hm F

theorem prefix_far_open : ∀ i, IsOpen (prefixFarFamily m hm F i) :=
  DoubleFarCupOneCap.far_open (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
theorem prefix_near_open : IsOpen (prefixNearSet m hm F) :=
  (NativeOrderedDoubleCutSupported.near_open _ _).inter (NativeOrderedDoubleCutSupported.near_open _ _)
theorem prefix_cover : (⋃ i, prefixFarFamily m hm F i) ∪ prefixNearSet m hm F = Set.univ :=
  DoubleFarCupOneCap.common_cover (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))

theorem prefix_far_maps : ∀ i, Set.MapsTo (NativeRawClockMaps.prefixClock (m + 1))
    (prefixFarFamily m hm F i) (NativeOrderedScalarPullback.farFamily m hm F (Bool.not i)) := by
  intro i
  cases i <;> intro z h <;> exact h

theorem prefix_near_maps : Set.MapsTo (NativeRawClockMaps.prefixClock (m + 1))
    (prefixNearSet m hm F) (NativeOrderedScalarPullback.nearSet m hm F) := by
  intro z h
  exact ⟨h.2, h.1⟩

def prefixNearMap := restriction (NativeRawClockMaps.prefixClock (m + 1)) (prefixNearSet m hm F)
  (NativeOrderedScalarPullback.nearSet m hm F) (prefix_near_maps m hm F)

theorem prefix_near_square : prefixNearMap m hm F ≫ NativeOrderedDoubleCapCommon.joint m hm F = prefixJoint m hm F := rfl

theorem prefix_first_thom : cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (m + 1)
    (NativeOrderedDoubleCapCommon.firstThom m hm F) = prefixThom m hm F := by
  unfold NativeOrderedDoubleCapCommon.firstThom prefixThom NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  rfl

theorem prefix_last_thom : cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (m + 1)
    (NativeOrderedDoubleCapCommon.lastThom m hm F) = outerThom m hm F := by
  unfold NativeOrderedDoubleCapCommon.lastThom outerThom NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  rfl

theorem prefix_cup : cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) ((m + 1) + m + 1)
    (NativeOrderedScalarPullback.thomCup m hm F) =
    DoubleFarCupOneCap.rightCup (source (m + 1)) (m + 1) m (outerThom m hm F) (prefixThom m hm F) := by
  unfold NativeOrderedScalarPullback.thomCup DoubleFarCupOneCap.leftCup DoubleFarCupOneCap.rightCup
  rw [CupCapOrder.naturality, prefix_first_thom, prefix_last_thom]

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_test : cochainPullback (prefixNearMap m hm F) (NativeTripleGHTest.degree m a b k)
    (NativeOrderedDoubleCapCommon.test m hm F a b k E) = prefixTest m hm F a b k E := by
  rw [NativeOrderedDoubleCapCommon.test, ← pullback_comp, prefix_near_square]
  rfl

abbrev suffixFarFamily := DoubleFarCupOneCap.far (source (m + 1)) (outerFar m hm F) (suffixFar m hm F)
abbrev suffixNearSet := outerNear m hm F ∩ suffixNear m hm F

theorem suffix_far_open : ∀ i, IsOpen (suffixFarFamily m hm F i) :=
  DoubleFarCupOneCap.far_open (source (m + 1)) (outerFar m hm F) (suffixFar m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
theorem suffix_near_open : IsOpen (suffixNearSet m hm F) :=
  (NativeOrderedDoubleCutSupported.near_open _ _).inter (NativeOrderedDoubleCutSupported.near_open _ _)
theorem suffix_cover : (⋃ i, suffixFarFamily m hm F i) ∪ suffixNearSet m hm F = Set.univ :=
  DoubleFarCupOneCap.common_cover (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))

theorem suffix_far_maps : ∀ i, Set.MapsTo (NativeRawClockMaps.suffixClock (m + 1))
    (suffixFarFamily m hm F i) (NativeOrderedScalarPullback.farFamily m hm F (id i)) := by
  intro i
  cases i <;> intro z h <;> exact h

theorem suffix_near_maps : Set.MapsTo (NativeRawClockMaps.suffixClock (m + 1))
    (suffixNearSet m hm F) (NativeOrderedScalarPullback.nearSet m hm F) := by
  intro z h
  exact h

def suffixNearMap := restriction (NativeRawClockMaps.suffixClock (m + 1)) (suffixNearSet m hm F)
  (NativeOrderedScalarPullback.nearSet m hm F) (suffix_near_maps m hm F)

theorem suffix_near_square : suffixNearMap m hm F ≫ NativeOrderedDoubleCapCommon.joint m hm F = suffixJoint m hm F := rfl

theorem suffix_first_thom : cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (m + 1)
    (NativeOrderedDoubleCapCommon.firstThom m hm F) = outerThom m hm F := by
  unfold NativeOrderedDoubleCapCommon.firstThom outerThom NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  rfl

theorem suffix_last_thom : cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (m + 1)
    (NativeOrderedDoubleCapCommon.lastThom m hm F) = suffixThom m hm F := by
  unfold NativeOrderedDoubleCapCommon.lastThom suffixThom NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  rfl

theorem suffix_cup : cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) ((m + 1) + m + 1)
    (NativeOrderedScalarPullback.thomCup m hm F) =
    DoubleFarCupOneCap.leftCup (source (m + 1)) (m + 1) m (outerThom m hm F) (suffixThom m hm F) := by
  unfold NativeOrderedScalarPullback.thomCup DoubleFarCupOneCap.leftCup
  rw [CupCapOrder.naturality, suffix_first_thom, suffix_last_thom]

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem suffix_test : cochainPullback (suffixNearMap m hm F) (NativeTripleGHTest.degree m a b k)
    (NativeOrderedDoubleCapCommon.test m hm F a b k E) = suffixTest m hm F a b k E := by
  rw [NativeOrderedDoubleCapCommon.test, ← pullback_comp, suffix_near_square]
  rfl

end
end Finsler.NativeRawOrderedCupGeometry
