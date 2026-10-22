module

public import Finsler.Loop.NativeRawClockMaps
public import Finsler.Loop.NativeSequentialDoubleCapOutputComparison
public import Finsler.Loop.NativeSuffixPostponedAlignment

/-! The original final-near maps pull back exactly the SAME Stage95
GH test. This includes the real degree transport used in Stage97,
not just equality of the numerical degrees. -/
@[expose] public section
namespace Finsler.NativeRawClockTestAlignment
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 450000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def prefixNear : TopCat.of (NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) (radius m hm F)) ⟶
    NativeOrderedDoubleCutCochain.domain m hm F := TopCat.ofHom
  ⟨fun z => NativeSequentialCutParameters.prefixCommon (prefixFinal m hm F z),
    NativeSequentialCutParameters.continuous_prefixCommon.comp (prefixFinal m hm F).hom.continuous⟩

def suffixNear : TopCat.of (NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) (radius m hm F)) ⟶
    NativeOrderedDoubleCutCochain.domain m hm F := TopCat.ofHom
  ⟨fun z => NativeSequentialCutParameters.suffixCommon (suffixFinal m hm F z),
    NativeSequentialCutParameters.continuous_suffixCommon.comp (suffixFinal m hm F).hom.continuous⟩

theorem prefix_triple : prefixNear m hm F ≫
    NativeSequentialTripleComparison.commonTriple (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) =
    prefixFinal m hm F ≫ NativeSequentialCollarGeometry.prefixCommon m hm F := rfl

theorem suffix_triple : suffixNear m hm F ≫
    NativeSequentialTripleComparison.commonTriple (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) =
    suffixFinal m hm F ≫ NativeSequentialCollarGeometry.suffixCommon m hm F := rfl

theorem prefix_source : prefixNear m hm F ≫ SupportedCap.subspaceMap
    (NativeOrderedDoubleCutGeometry.source (m + 1))
    (NativeOrderedDoubleCutGeometry.near (m + 1) (radius m hm F)) =
    SupportedCap.subspaceMap (outerSpace m hm F)
      (NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) (radius m hm F)) ≫
      NativeRawClockMaps.outerInclusion m hm F ≫ NativeRawClockMaps.prefixClock (m + 1) := rfl

theorem suffix_source : suffixNear m hm F ≫ SupportedCap.subspaceMap
    (NativeOrderedDoubleCutGeometry.source (m + 1))
    (NativeOrderedDoubleCutGeometry.near (m + 1) (radius m hm F)) =
    SupportedCap.subspaceMap (outerSpace m hm F)
      (NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) (radius m hm F)) ≫
      NativeRawClockMaps.outerInclusion m hm F ≫ NativeRawClockMaps.suffixClock (m + 1) := rfl

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem common_test : cochainPullback
    (NativeSequentialTripleComparison.commonTriple (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F))
    (NativeTripleGHTest.degree m a b k) (NativeTripleGHTest.test m hm F a b k E) =
    NativeOrderedDoubleCutCochain.tests m hm F a b k E := by
  rw [NativeTripleGHTest.test, cochainCup_naturality, cochainCup_naturality]
  simp only [← pullback_comp]
  rfl

theorem prefix_test : cochainPullback (prefixFinal m hm F) _
    (cochainPullback (NativeSequentialCollarGeometry.prefixCommon m hm F) _
      (NativeTripleGHTest.test m hm F a b k E)) =
    cochainPullback (prefixNear m hm F) _ (NativeOrderedDoubleCutCochain.tests m hm F a b k E) := by
  rw [← common_test m hm F a b k E]
  simp only [← pullback_comp]
  rw [prefix_triple]

theorem suffix_test : cochainPullback (suffixFinal m hm F) _
    (cochainPullback (NativeSequentialCollarGeometry.suffixCommon m hm F) _
      (NativeTripleGHTest.test m hm F a b k E)) =
    cochainPullback (suffixNear m hm F) _ (NativeOrderedDoubleCutCochain.tests m hm F a b k E) := by
  rw [← common_test m hm F a b k E]
  simp only [← pullback_comp]
  rw [suffix_triple]

theorem prefix_input : cochainPullback (prefixFinal m hm F) _
    (cochainPullback (NativeSequentialCollarGeometry.prefixCommon m hm F) _
      (NativeSequentialGHGlobalComparison.input m hm F a b k E)) =
    CochainDegreeTransport.pre _ (NativeSequentialGHGlobalComparison.degree_match m hm a b k)
      (cochainPullback (prefixNear m hm F) _ (NativeOrderedDoubleCutCochain.tests m hm F a b k E)) := by
  rw [NativeSequentialGHGlobalComparison.input, NativeSuffixPostponedAlignment.pre_pullback,
    NativeSuffixPostponedAlignment.pre_pullback, prefix_test]

theorem suffix_input : cochainPullback (suffixFinal m hm F) _
    (cochainPullback (NativeSequentialCollarGeometry.suffixCommon m hm F) _
      (NativeSequentialGHGlobalComparison.input m hm F a b k E)) =
    CochainDegreeTransport.pre _ (NativeSequentialGHGlobalComparison.degree_match m hm a b k)
      (cochainPullback (suffixNear m hm F) _ (NativeOrderedDoubleCutCochain.tests m hm F a b k E)) := by
  rw [NativeSequentialGHGlobalComparison.input, NativeSuffixPostponedAlignment.pre_pullback,
    NativeSuffixPostponedAlignment.pre_pullback, suffix_test]

end
end Finsler.NativeRawClockTestAlignment
