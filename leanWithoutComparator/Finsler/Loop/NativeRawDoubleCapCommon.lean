module

public import Finsler.Loop.NativeRawClockSupportedAlignment
public import Finsler.Loop.OriginalDoubleCapCarrier

/-! BOTH actual original postponed two-stage cochains reduce to their
raw common cup cap by the actual subdivision primitive. The primitive
vanishes on the FULL inverse diagonal, so the comparison applies to
relative chains with a genuine boundary factorization there. -/
@[expose] public section
namespace Finsler.NativeRawDoubleCapCommon
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages
open Finsler.NativeRawClockDoubleGeometry Finsler.NativeRawClockSupportedAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixCoupled := OriginalDoubleCapCommonComparison.coupled (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (prefixThom m hm F)
  (outer_supported m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)
def prefixPrimitive := OriginalDoubleCapCommonComparison.primitive (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (prefixThom m hm F)
  (outer_supported m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)
def prefixDiagonal : Set (source (m + 1)) :=
  (NativeRawClockMaps.prefixClock (m + 1)) ⁻¹' NativeOrderedDoubleCutSupported.diagonal m

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixPrimitive m hm F a b k E) =
    prefixSequential m hm F a b k E - prefixCoupled m hm F a b k E :=
  OriginalDoubleCapCommonComparison.boundary (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (prefixThom m hm F)
  (outer_supported m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)
    (NativeOrderedDoubleCutSupported.thom_closed _ _ _) (NativeOrderedDoubleCutSupported.thom_closed _ _ _)
    (prefix_test_closed m hm F a b k E hE)

theorem prefix_stage97_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixPrimitive m hm F a b k E) =
    CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
      (NativeSequentialDoubleCapOutputComparison.prefixCommon m hm F a b k E) - prefixCoupled m hm F a b k E := by
  rw [prefix_stage97_compare]
  exact prefix_boundary m hm F a b k E hE

theorem prefix_diagonal_test_zero : cochainPullback
    (restriction (SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m))
      ((SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m)) ⁻¹' (outerNear m hm F ∩ prefixNear m hm F))
      (outerNear m hm F ∩ prefixNear m hm F) (fun _ h => h)) (testDegree m a b k) (prefixTest m hm F a b k E) = 0 := by
  let f := restriction (SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m))
    ((SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m)) ⁻¹' (outerNear m hm F ∩ prefixNear m hm F))
    (outerNear m hm F ∩ prefixNear m hm F) (fun _ h => h)
  let d : TopCat.of ((SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m)) ⁻¹'
      (outerNear m hm F ∩ prefixNear m hm F)) ⟶
      NativeOrderedDoubleCutDiagonal.diagonalDomain (m + 1) (radius m hm F) := TopCat.ofHom
    ⟨fun z => ⟨prefixJoint m hm F (f z), z.val.property⟩,
      ((prefixJoint m hm F).hom.continuous.comp f.hom.continuous).subtype_mk _⟩
  have he : f ≫ prefixJoint m hm F = d ≫ NativeOrderedDoubleCutDiagonal.inclusion (m + 1) (radius m hm F) := rfl
  change cochainPullback f _ (prefixTest m hm F a b k E) = 0
  rw [prefixTest, ← pullback_comp, he, pullback_comp, NativeOrderedDoubleCutCochain.tests_diagonal_zero]
  change (push d).f _ ≫ 0 = 0
  exact comp_zero

theorem prefix_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m)) (index m a b k) (prefixPrimitive m hm F a b k E) = 0 :=
  OriginalDoubleCapCarrier.primitive_zero (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (prefixThom m hm F)
  (outer_supported m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)
    (prefixDiagonal m) (prefix_diagonal_test_zero m hm F a b k E)

theorem prefix_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (prefixDiagonal m))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m))).f (index m a b k)) :
    c ≫ CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
      (NativeSequentialDoubleCapOutputComparison.prefixCommon m hm F a b k E) = c ≫ prefixCoupled m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (prefix_stage97_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    prefixPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, Category.assoc] at hb
  have hz : (push (SupportedCap.subspaceMap (source (m + 1)) (prefixDiagonal m))).f (index m a b k) ≫
      prefixPrimitive m hm F a b k E = 0 := prefix_primitive_diagonal_zero m hm F a b k E
  rw [hz, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

def suffixCoupled := OriginalDoubleCapCommonComparison.coupled (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (suffixThom m hm F)
  (outer_supported m hm F) (suffix_supported m hm F) (suffixTest m hm F a b k E)
def suffixPrimitive := OriginalDoubleCapCommonComparison.primitive (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (suffixThom m hm F)
  (outer_supported m hm F) (suffix_supported m hm F) (suffixTest m hm F a b k E)
def suffixDiagonal : Set (source (m + 1)) :=
  (NativeRawClockMaps.suffixClock (m + 1)) ⁻¹' NativeOrderedDoubleCutSupported.diagonal m

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixPrimitive m hm F a b k E) =
    suffixSequential m hm F a b k E - suffixCoupled m hm F a b k E :=
  OriginalDoubleCapCommonComparison.boundary (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (suffixThom m hm F)
  (outer_supported m hm F) (suffix_supported m hm F) (suffixTest m hm F a b k E)
    (NativeOrderedDoubleCutSupported.thom_closed _ _ _) (NativeOrderedDoubleCutSupported.thom_closed _ _ _)
    (suffix_test_closed m hm F a b k E hE)

theorem suffix_stage97_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixPrimitive m hm F a b k E) =
    CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
      (NativeSequentialDoubleCapOutputComparison.suffixCommon m hm F a b k E) - suffixCoupled m hm F a b k E := by
  rw [suffix_stage97_compare]
  exact suffix_boundary m hm F a b k E hE

theorem suffix_diagonal_test_zero : cochainPullback
    (restriction (SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m))
      ((SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m)) ⁻¹' (outerNear m hm F ∩ suffixNear m hm F))
      (outerNear m hm F ∩ suffixNear m hm F) (fun _ h => h)) (testDegree m a b k) (suffixTest m hm F a b k E) = 0 := by
  let f := restriction (SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m))
    ((SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m)) ⁻¹' (outerNear m hm F ∩ suffixNear m hm F))
    (outerNear m hm F ∩ suffixNear m hm F) (fun _ h => h)
  let d : TopCat.of ((SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m)) ⁻¹'
      (outerNear m hm F ∩ suffixNear m hm F)) ⟶
      NativeOrderedDoubleCutDiagonal.diagonalDomain (m + 1) (radius m hm F) := TopCat.ofHom
    ⟨fun z => ⟨suffixJoint m hm F (f z), z.val.property⟩,
      ((suffixJoint m hm F).hom.continuous.comp f.hom.continuous).subtype_mk _⟩
  have he : f ≫ suffixJoint m hm F = d ≫ NativeOrderedDoubleCutDiagonal.inclusion (m + 1) (radius m hm F) := rfl
  change cochainPullback f _ (suffixTest m hm F a b k E) = 0
  rw [suffixTest, ← pullback_comp, he, pullback_comp, NativeOrderedDoubleCutCochain.tests_diagonal_zero]
  change (push d).f _ ≫ 0 = 0
  exact comp_zero

theorem suffix_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m)) (index m a b k) (suffixPrimitive m hm F a b k E) = 0 :=
  OriginalDoubleCapCarrier.primitive_zero (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (suffixThom m hm F)
  (outer_supported m hm F) (suffix_supported m hm F) (suffixTest m hm F a b k E)
    (suffixDiagonal m) (suffix_diagonal_test_zero m hm F a b k E)

theorem suffix_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (suffixDiagonal m))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m))).f (index m a b k)) :
    c ≫ CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
      (NativeSequentialDoubleCapOutputComparison.suffixCommon m hm F a b k E) = c ≫ suffixCoupled m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (suffix_stage97_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    suffixPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, Category.assoc] at hb
  have hz : (push (SupportedCap.subspaceMap (source (m + 1)) (suffixDiagonal m))).f (index m a b k) ≫
      suffixPrimitive m hm F a b k E = 0 := suffix_primitive_diagonal_zero m hm F a b k E
  rw [hz, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.NativeRawDoubleCapCommon
