module

public import Finsler.Loop.NativeRawClockTestAlignment
public import Finsler.Loop.SupportedCapSetTransport
public import Finsler.Loop.OriginalDoubleCapCommonComparison

/-! Actual global raw-clock neighborhoods and their common-near GH
input. The inner pulled Thom is the original half-cut Thom; open
near/far domains are equal, including every endpoint. -/
@[expose] public section
namespace Finsler.NativeRawClockDoubleGeometry
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev outerFar := NativeOrderedDoubleCutSupported.far (firstParameter (m + 1))
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev outerNear := NativeOrderedDoubleCutSupported.near (firstParameter (m + 1)) (radius m hm F)
def outerThom := NativeOrderedDoubleCutSupported.thom (firstParameter (m + 1))
  (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
theorem outer_supported : cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (outerFar m hm F))
    (m + 1) (outerThom m hm F) = 0 := NativeOrderedDoubleCutSupported.thom_supported _ _ _

def prefixGlobal : source (m + 1) ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  NativeRawClockMaps.prefixClock (m + 1) ≫ NativeOrderedDoubleCutGeometry.firstParameter (m + 1)
abbrev prefixFar := NativeOrderedDoubleCutSupported.far (prefixGlobal m)
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev prefixNear := NativeOrderedDoubleCutSupported.near (prefixGlobal m) (radius m hm F)
def prefixThom := NativeOrderedDoubleCutSupported.thom (prefixGlobal m)
  (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
theorem prefix_supported : cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFar m hm F))
    (m + 1) (prefixThom m hm F) = 0 := NativeOrderedDoubleCutSupported.thom_supported _ _ _

theorem prefix_inner_far : OriginalDoubleSupportedCap.secondFar (source (m + 1))
    (outerNear m hm F) (prefixFar m hm F) =
    NativeOrderedDoubleCutSupported.far (prefixParameter m hm F) (NativeOrderedDoubleCutSupported.thomRadius m hm F) :=
  NativeRawClockMaps.prefix_inner_far m hm F _

theorem prefix_inner_near : OriginalDoubleSupportedCap.secondNear (source (m + 1))
    (outerNear m hm F) (prefixNear m hm F) =
    NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) (radius m hm F) :=
  NativeRawClockMaps.prefix_inner_near m hm F _

theorem prefix_inner_thom : cochainPullback (NativeRawClockMaps.outerInclusion m hm F) (m + 1)
    (prefixThom m hm F) = NativeOrderedDoubleCutSupported.thom (prefixParameter m hm F)
      (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) := by
  unfold prefixThom NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  exact (prefix_thom_original_clock m hm F).symm

def prefixJoint : TopCat.of (outerNear m hm F ∩ prefixNear m hm F : Set (source (m + 1))) ⟶
    NativeOrderedDoubleCutCochain.domain m hm F := TopCat.ofHom
  ⟨fun z => ⟨NativeRawClockMaps.prefixClock (m + 1) z.val, z.property.2, z.property.1⟩,
    ((NativeRawClockMaps.prefixClock (m + 1)).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def prefixTransport := SupportedCapSetTransport.nearMap (outerSpace m hm F)
  (NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) (radius m hm F))
  (OriginalDoubleSupportedCap.secondNear (source (m + 1)) (outerNear m hm F) (prefixNear m hm F))
  (prefix_inner_near m hm F).symm

theorem prefix_near_square : prefixTransport m hm F ≫
    OriginalDoubleSupportedCap.jointMap (source (m + 1)) (outerNear m hm F) (prefixNear m hm F) ≫
    prefixJoint m hm F = NativeRawClockTestAlignment.prefixNear m hm F := rfl

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixTest := cochainPullback (prefixJoint m hm F) (NativeTripleGHTest.degree m a b k)
  (NativeOrderedDoubleCutCochain.tests m hm F a b k E)

theorem prefix_test_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (prefixTest m hm F a b k E) = 0 :=
  pullback_closed _ _ _ (NativeOrderedDoubleCutCochain.tests_closed m hm F a b k E hE)

theorem prefix_test_transport : cochainPullback (prefixTransport m hm F) _
    (cochainPullback (OriginalDoubleSupportedCap.jointMap (source (m + 1)) (outerNear m hm F) (prefixNear m hm F)) _
      (prefixTest m hm F a b k E)) =
    cochainPullback (NativeRawClockTestAlignment.prefixNear m hm F) _
      (NativeOrderedDoubleCutCochain.tests m hm F a b k E) := by
  unfold prefixTest
  simp only [← pullback_comp]
  rw [prefix_near_square]

def suffixGlobal : source (m + 1) ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  NativeRawClockMaps.suffixClock (m + 1) ≫ NativeOrderedDoubleCutGeometry.lastParameter (m + 1)
abbrev suffixFar := NativeOrderedDoubleCutSupported.far (suffixGlobal m)
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev suffixNear := NativeOrderedDoubleCutSupported.near (suffixGlobal m) (radius m hm F)
def suffixThom := NativeOrderedDoubleCutSupported.thom (suffixGlobal m)
  (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
theorem suffix_supported : cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFar m hm F))
    (m + 1) (suffixThom m hm F) = 0 := NativeOrderedDoubleCutSupported.thom_supported _ _ _

theorem suffix_inner_far : OriginalDoubleSupportedCap.secondFar (source (m + 1))
    (outerNear m hm F) (suffixFar m hm F) =
    NativeOrderedDoubleCutSupported.far (suffixParameter m hm F) (NativeOrderedDoubleCutSupported.thomRadius m hm F) :=
  NativeRawClockMaps.suffix_inner_far m hm F _

theorem suffix_inner_near : OriginalDoubleSupportedCap.secondNear (source (m + 1))
    (outerNear m hm F) (suffixNear m hm F) =
    NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) (radius m hm F) :=
  NativeRawClockMaps.suffix_inner_near m hm F _

theorem suffix_inner_thom : cochainPullback (NativeRawClockMaps.outerInclusion m hm F) (m + 1)
    (suffixThom m hm F) = NativeOrderedDoubleCutSupported.thom (suffixParameter m hm F)
      (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) := by
  unfold suffixThom NativeOrderedDoubleCutSupported.thom
  rw [← pullback_comp]
  exact (suffix_thom_original_clock m hm F).symm

def suffixJoint : TopCat.of (outerNear m hm F ∩ suffixNear m hm F : Set (source (m + 1))) ⟶
    NativeOrderedDoubleCutCochain.domain m hm F := TopCat.ofHom
  ⟨fun z => ⟨NativeRawClockMaps.suffixClock (m + 1) z.val, z.property.1, z.property.2⟩,
    ((NativeRawClockMaps.suffixClock (m + 1)).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def suffixTransport := SupportedCapSetTransport.nearMap (outerSpace m hm F)
  (NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) (radius m hm F))
  (OriginalDoubleSupportedCap.secondNear (source (m + 1)) (outerNear m hm F) (suffixNear m hm F))
  (suffix_inner_near m hm F).symm

theorem suffix_near_square : suffixTransport m hm F ≫
    OriginalDoubleSupportedCap.jointMap (source (m + 1)) (outerNear m hm F) (suffixNear m hm F) ≫
    suffixJoint m hm F = NativeRawClockTestAlignment.suffixNear m hm F := rfl

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def suffixTest := cochainPullback (suffixJoint m hm F) (NativeTripleGHTest.degree m a b k)
  (NativeOrderedDoubleCutCochain.tests m hm F a b k E)

theorem suffix_test_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (suffixTest m hm F a b k E) = 0 :=
  pullback_closed _ _ _ (NativeOrderedDoubleCutCochain.tests_closed m hm F a b k E hE)

theorem suffix_test_transport : cochainPullback (suffixTransport m hm F) _
    (cochainPullback (OriginalDoubleSupportedCap.jointMap (source (m + 1)) (outerNear m hm F) (suffixNear m hm F)) _
      (suffixTest m hm F a b k E)) =
    cochainPullback (NativeRawClockTestAlignment.suffixNear m hm F) _
      (NativeOrderedDoubleCutCochain.tests m hm F a b k E) := by
  unfold suffixTest
  simp only [← pullback_comp]
  rw [suffix_near_square]

end
end Finsler.NativeRawClockDoubleGeometry
