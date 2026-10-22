module

public import Finsler.Loop.NativeRawClockDoubleGeometry

/-! Identify both ORIGINAL supported Thom stages, with the SAME final
GH test, with the genuine double-cap construction on each raw source.
Every source/test degree transport remains explicit. This concerns
postponed tests; complete interleaved time insertion is separate. -/
@[expose] public section
namespace Finsler.NativeRawClockSupportedAlignment
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockDoubleGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000

theorem pre_trans (X : TopCat.{0}) {i j k : ℕ} (h : i = j) (h' : j = k)
    (T : singularCochainGroup (ZMod 2) X k) :
    CochainDegreeTransport.pre X h (CochainDegreeTransport.pre X h' T) =
    CochainDegreeTransport.pre X (h.trans h') T := by
  subst k j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)
abbrev testDegree := NativeTripleGHTest.degree m a b k
abbrev index := ((m + 1) + m) + testDegree m a b k
abbrev total := (m + 1) + ((m + 1) + testDegree m a b k)

theorem degree_match : index m a b k + 1 = total m a b k := by dsimp [index, total]; omega
include hm in
theorem stage97_degree : index m a b k + 1 =
    (m + 1) + ((m + 1) + (NativeSequentialGHGlobalComparison.testDegree m a b k + 1)) := by
  rw [NativeSequentialGHGlobalComparison.degree_match m hm a b k]
  exact degree_match m a b k

def prefixInner := OriginalDoubleSupportedCap.inner (source (m + 1)) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) (testDegree m a b k) (prefixThom m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)
def prefixSequential := OriginalDoubleCapCommonComparison.sequential (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (prefixThom m hm F)
  (outer_supported m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)

def prefixCanonical : singularCochainGroup (ZMod 2) (source (m + 1)) (total m a b k) :=
  (firstOperation m hm F).component ((m + 1) + testDegree m a b k) ≫
    (prefixOperation m hm F).component (testDegree m a b k) ≫
      cochainPullback (NativeRawClockTestAlignment.prefixNear m hm F) _
        (NativeOrderedDoubleCutCochain.tests m hm F a b k E)

theorem prefix_inner_eq : (prefixOperation m hm F).component (testDegree m a b k) ≫
    cochainPullback (NativeRawClockTestAlignment.prefixNear m hm F) _
      (NativeOrderedDoubleCutCochain.tests m hm F a b k E) = prefixInner m hm F a b k E := by
  have h := SupportedCapSetTransport.scalar (outerSpace m hm F)
    (NativeOrderedDoubleCutSupported.far (prefixParameter m hm F) (NativeOrderedDoubleCutSupported.thomRadius m hm F))
    (NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) (radius m hm F))
    (OriginalDoubleSupportedCap.secondFar (source (m + 1)) (outerNear m hm F) (prefixFar m hm F))
    (OriginalDoubleSupportedCap.secondNear (source (m + 1)) (outerNear m hm F) (prefixNear m hm F))
    (NativeOrderedDoubleCutSupported.far_open (prefixParameter m hm F) _)
    (NativeOrderedDoubleCutSupported.near_open (prefixParameter m hm F) _)
    ((NativeOrderedDoubleCutSupported.far_open (prefixGlobal m) _).preimage (NativeRawClockMaps.outerInclusion m hm F).hom.continuous)
    ((NativeOrderedDoubleCutSupported.near_open (prefixGlobal m) _).preimage (NativeRawClockMaps.outerInclusion m hm F).hom.continuous)
    (NativeOrderedDoubleCutSupported.cover (prefixParameter m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (OriginalDoubleSupportedCap.second_cover (source (m + 1)) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
      (NativeOrderedDoubleCutSupported.cover (prefixGlobal m) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)))
    (prefix_inner_far m hm F).symm (prefix_inner_near m hm F).symm
    (m + 1) (testDegree m a b k) ((m + 1) + testDegree m a b k) rfl
    (NativeOrderedDoubleCutSupported.thom (prefixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
    (cochainPullback (NativeRawClockMaps.outerInclusion m hm F) (m + 1) (prefixThom m hm F))
    (NativeOrderedDoubleCutSupported.thom_supported (prefixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
    (pullback_support (NativeRawClockMaps.outerInclusion m hm F)
      (OriginalDoubleSupportedCap.secondFar (source (m + 1)) (outerNear m hm F) (prefixFar m hm F))
      (prefixFar m hm F) (fun _ h => h) (m + 1) (prefixThom m hm F) (prefix_supported m hm F))
    (prefix_inner_thom m hm F).symm
    (cochainPullback (OriginalDoubleSupportedCap.jointMap (source (m + 1)) (outerNear m hm F) (prefixNear m hm F)) _
      (prefixTest m hm F a b k E))
  change _ ≫ cochainPullback (prefixTransport m hm F) _ _ = prefixInner m hm F a b k E at h
  rw [prefix_test_transport] at h
  exact h

theorem prefix_canonical_compare : CochainDegreeTransport.pre (source (m + 1)) (degree_match m a b k)
    (prefixCanonical m hm F a b k E) = prefixSequential m hm F a b k E := by
  unfold prefixCanonical
  rw [prefix_inner_eq]
  exact NativeSuffixPostponedAlignment.pre_cut (source (m + 1)) (outerFar m hm F) (outerNear m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (m + 1) ((m + 1) + testDegree m a b k) (index m a b k + 1) (total m a b k)
    (by dsimp [index]; omega) rfl (degree_match m a b k) (outerThom m hm F) (outer_supported m hm F)
    (prefixInner m hm F a b k E)

theorem prefix_stage97_canonical : CochainDegreeTransport.pre (source (m + 1))
    (congrArg (fun t => (m + 1) + ((m + 1) + t)) (NativeSequentialGHGlobalComparison.degree_match m hm a b k))
    (prefixCanonical m hm F a b k E) = NativeSequentialDoubleCapOutputComparison.prefixCommon m hm F a b k E := by
  unfold prefixCanonical NativeSequentialDoubleCapOutputComparison.prefixCommon
  rw [NativeRawClockTestAlignment.prefix_input,
    NativeSuffixPostponedAlignment.pre_lowering, NativeSuffixPostponedAlignment.pre_lowering]
  exact congrArg (fun t => (m + 1) + t) (NativeSequentialGHGlobalComparison.degree_match m hm a b k)

theorem prefix_stage97_compare : CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
    (NativeSequentialDoubleCapOutputComparison.prefixCommon m hm F a b k E) = prefixSequential m hm F a b k E := by
  rw [← prefix_stage97_canonical, pre_trans]
  exact prefix_canonical_compare m hm F a b k E

def suffixInner := OriginalDoubleSupportedCap.inner (source (m + 1)) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) (testDegree m a b k) (suffixThom m hm F) (suffix_supported m hm F) (suffixTest m hm F a b k E)
def suffixSequential := OriginalDoubleCapCommonComparison.sequential (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (suffixThom m hm F)
  (outer_supported m hm F) (suffix_supported m hm F) (suffixTest m hm F a b k E)

def suffixCanonical : singularCochainGroup (ZMod 2) (source (m + 1)) (total m a b k) :=
  (firstOperation m hm F).component ((m + 1) + testDegree m a b k) ≫
    (suffixOperation m hm F).component (testDegree m a b k) ≫
      cochainPullback (NativeRawClockTestAlignment.suffixNear m hm F) _
        (NativeOrderedDoubleCutCochain.tests m hm F a b k E)

theorem suffix_inner_eq : (suffixOperation m hm F).component (testDegree m a b k) ≫
    cochainPullback (NativeRawClockTestAlignment.suffixNear m hm F) _
      (NativeOrderedDoubleCutCochain.tests m hm F a b k E) = suffixInner m hm F a b k E := by
  have h := SupportedCapSetTransport.scalar (outerSpace m hm F)
    (NativeOrderedDoubleCutSupported.far (suffixParameter m hm F) (NativeOrderedDoubleCutSupported.thomRadius m hm F))
    (NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) (radius m hm F))
    (OriginalDoubleSupportedCap.secondFar (source (m + 1)) (outerNear m hm F) (suffixFar m hm F))
    (OriginalDoubleSupportedCap.secondNear (source (m + 1)) (outerNear m hm F) (suffixNear m hm F))
    (NativeOrderedDoubleCutSupported.far_open (suffixParameter m hm F) _)
    (NativeOrderedDoubleCutSupported.near_open (suffixParameter m hm F) _)
    ((NativeOrderedDoubleCutSupported.far_open (suffixGlobal m) _).preimage (NativeRawClockMaps.outerInclusion m hm F).hom.continuous)
    ((NativeOrderedDoubleCutSupported.near_open (suffixGlobal m) _).preimage (NativeRawClockMaps.outerInclusion m hm F).hom.continuous)
    (NativeOrderedDoubleCutSupported.cover (suffixParameter m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (OriginalDoubleSupportedCap.second_cover (source (m + 1)) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
      (NativeOrderedDoubleCutSupported.cover (suffixGlobal m) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)))
    (suffix_inner_far m hm F).symm (suffix_inner_near m hm F).symm
    (m + 1) (testDegree m a b k) ((m + 1) + testDegree m a b k) rfl
    (NativeOrderedDoubleCutSupported.thom (suffixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
    (cochainPullback (NativeRawClockMaps.outerInclusion m hm F) (m + 1) (suffixThom m hm F))
    (NativeOrderedDoubleCutSupported.thom_supported (suffixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
    (pullback_support (NativeRawClockMaps.outerInclusion m hm F)
      (OriginalDoubleSupportedCap.secondFar (source (m + 1)) (outerNear m hm F) (suffixFar m hm F))
      (suffixFar m hm F) (fun _ h => h) (m + 1) (suffixThom m hm F) (suffix_supported m hm F))
    (suffix_inner_thom m hm F).symm
    (cochainPullback (OriginalDoubleSupportedCap.jointMap (source (m + 1)) (outerNear m hm F) (suffixNear m hm F)) _
      (suffixTest m hm F a b k E))
  change _ ≫ cochainPullback (suffixTransport m hm F) _ _ = suffixInner m hm F a b k E at h
  rw [suffix_test_transport] at h
  exact h

theorem suffix_canonical_compare : CochainDegreeTransport.pre (source (m + 1)) (degree_match m a b k)
    (suffixCanonical m hm F a b k E) = suffixSequential m hm F a b k E := by
  unfold suffixCanonical
  rw [suffix_inner_eq]
  exact NativeSuffixPostponedAlignment.pre_cut (source (m + 1)) (outerFar m hm F) (outerNear m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (m + 1) ((m + 1) + testDegree m a b k) (index m a b k + 1) (total m a b k)
    (by dsimp [index]; omega) rfl (degree_match m a b k) (outerThom m hm F) (outer_supported m hm F)
    (suffixInner m hm F a b k E)

theorem suffix_stage97_canonical : CochainDegreeTransport.pre (source (m + 1))
    (congrArg (fun t => (m + 1) + ((m + 1) + t)) (NativeSequentialGHGlobalComparison.degree_match m hm a b k))
    (suffixCanonical m hm F a b k E) = NativeSequentialDoubleCapOutputComparison.suffixCommon m hm F a b k E := by
  unfold suffixCanonical NativeSequentialDoubleCapOutputComparison.suffixCommon
  rw [NativeRawClockTestAlignment.suffix_input,
    NativeSuffixPostponedAlignment.pre_lowering, NativeSuffixPostponedAlignment.pre_lowering]
  exact congrArg (fun t => (m + 1) + t) (NativeSequentialGHGlobalComparison.degree_match m hm a b k)

theorem suffix_stage97_compare : CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
    (NativeSequentialDoubleCapOutputComparison.suffixCommon m hm F a b k E) = suffixSequential m hm F a b k E := by
  rw [← suffix_stage97_canonical, pre_trans]
  exact suffix_canonical_compare m hm F a b k E

end
end Finsler.NativeRawClockSupportedAlignment
