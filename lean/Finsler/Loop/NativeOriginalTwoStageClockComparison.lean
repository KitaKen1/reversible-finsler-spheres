module

public import Finsler.Loop.NativeRawStage101Bridge
public import Finsler.Loop.NativeRawOriginalScalarReduction

/-! BOTH original two-supported-Thom operations with postponed SAME
GH tests are compared with the raw-clock pullbacks of the SAME sealed
Stage95 ordered cochain. Every subdivision/cup-one/output correction
and actual degree transport is retained. The common-output comparison
is relative to the full inverse diagonal. The original-output total
comparison is proved on all cycles; its full relative support and
complete interleaved sequential time insertion remain separate. -/
@[expose] public section
namespace Finsler.NativeOriginalTwoStageClockComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockSupportedAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixCommonInput := CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
  (NativeSequentialDoubleCapOutputComparison.prefixCommon m hm F a b k E)

def prefixOrderedInput := cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (index m a b k + 1)
  (CochainDegreeTransport.pre (NativeOrderedDoubleCapCommon.source m) (NativeOrderedDoubleCapCommon.degree_match m a b k)
    (NativeOrderedDoubleCutSupported.cochain m hm F a b k E))

def prefixCommonPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E + NativeRawStage101Bridge.prefixPrimitive m hm F a b k E -
    NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E

def prefixOriginalPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  NativeRawOriginalScalarReduction.prefixPrimitive m hm F a b k E + NativeRawStage101Bridge.prefixPrimitive m hm F a b k E -
    NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E

theorem prefix_common_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixCommonPrimitive m hm F a b k E) =
    prefixCommonInput m hm F a b k E - prefixOrderedInput m hm F a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom ((_ + _) - _) = _
  rw [map_sub, map_add]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E) +
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawStage101Bridge.prefixPrimitive m hm F a b k E) -
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E) = _
  rw [NativeRawDoubleCapCommon.prefix_stage97_boundary m hm F a b k E hE,
    NativeRawStage101Bridge.prefix_boundary m hm F a b k E hE,
    NativeOrderedScalarPullback.original_boundary m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E hE]
  change (prefixCommonInput m hm F a b k E - _) + (_ - _) - (prefixOrderedInput m hm F a b k E - _) = _
  abel

theorem prefix_common_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
    (prefixCommonPrimitive m hm F a b k E) = 0 := by
  have hz : cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m))
      (index m a b k) (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E) = 0 :=
    NativeOrderedScalarPullback.primitive_diagonal_zero m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)).op).f (index m a b k)).hom ((_ + _) - _) = 0
  rw [map_sub, map_add]
  change cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
      (NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E) +
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
      (NativeRawStage101Bridge.prefixPrimitive m hm F a b k E) -
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
      (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E) = 0
  rw [NativeRawDoubleCapCommon.prefix_primitive_diagonal_zero, NativeRawStage101Bridge.prefix_primitive_diagonal_zero,
    hz, add_zero, sub_self]

theorem prefix_common_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (NativeRawDoubleCapCommon.prefixDiagonal m))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m))).f (index m a b k)) :
    c ≫ prefixCommonInput m hm F a b k E = c ≫ prefixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (prefix_common_boundary m hm F a b k E hE)
  have hz : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m))).f (index m a b k) ≫
      prefixCommonPrimitive m hm F a b k E = 0 := prefix_common_primitive_diagonal_zero m hm F a b k E
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫ prefixCommonPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, Category.assoc, hz, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

theorem prefix_original_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixOriginalPrimitive m hm F a b k E) =
    NativeRawOriginalScalarReduction.prefixOriginal m hm F a b k E - prefixOrderedInput m hm F a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom ((_ + _) - _) = _
  rw [map_sub, map_add]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawOriginalScalarReduction.prefixPrimitive m hm F a b k E) +
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawStage101Bridge.prefixPrimitive m hm F a b k E) -
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E) = _
  rw [NativeRawOriginalScalarReduction.prefix_boundary m hm F a b k E hE,
    NativeRawStage101Bridge.prefix_boundary m hm F a b k E hE,
    NativeOrderedScalarPullback.original_boundary m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E hE]
  change (_ - _) + (_ - _) - (prefixOrderedInput m hm F a b k E - _) = _
  abel

theorem prefix_original_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) = 0) :
    c ≫ NativeRawOriginalScalarReduction.prefixOriginal m hm F a b k E = c ≫ prefixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (prefix_original_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫ prefixOriginalPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, zero_comp, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

def suffixCommonInput := CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
  (NativeSequentialDoubleCapOutputComparison.suffixCommon m hm F a b k E)

def suffixOrderedInput := cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (index m a b k + 1)
  (CochainDegreeTransport.pre (NativeOrderedDoubleCapCommon.source m) (NativeOrderedDoubleCapCommon.degree_match m a b k)
    (NativeOrderedDoubleCutSupported.cochain m hm F a b k E))

def suffixCommonPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E + NativeRawStage101Bridge.suffixPrimitive m hm F a b k E -
    NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E

def suffixOriginalPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  NativeRawOriginalScalarReduction.suffixPrimitive m hm F a b k E + NativeRawStage101Bridge.suffixPrimitive m hm F a b k E -
    NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E

theorem suffix_common_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixCommonPrimitive m hm F a b k E) =
    suffixCommonInput m hm F a b k E - suffixOrderedInput m hm F a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom ((_ + _) - _) = _
  rw [map_sub, map_add]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E) +
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawStage101Bridge.suffixPrimitive m hm F a b k E) -
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E) = _
  rw [NativeRawDoubleCapCommon.suffix_stage97_boundary m hm F a b k E hE,
    NativeRawStage101Bridge.suffix_boundary m hm F a b k E hE,
    NativeOrderedScalarPullback.original_boundary m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E hE]
  change (suffixCommonInput m hm F a b k E - _) + (_ - _) - (suffixOrderedInput m hm F a b k E - _) = _
  abel

theorem suffix_common_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
    (suffixCommonPrimitive m hm F a b k E) = 0 := by
  have hz : cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m))
      (index m a b k) (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E) = 0 :=
    NativeOrderedScalarPullback.primitive_diagonal_zero m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)).op).f (index m a b k)).hom ((_ + _) - _) = 0
  rw [map_sub, map_add]
  change cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
      (NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E) +
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
      (NativeRawStage101Bridge.suffixPrimitive m hm F a b k E) -
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
      (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E) = 0
  rw [NativeRawDoubleCapCommon.suffix_primitive_diagonal_zero, NativeRawStage101Bridge.suffix_primitive_diagonal_zero,
    hz, add_zero, sub_self]

theorem suffix_common_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (NativeRawDoubleCapCommon.suffixDiagonal m))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m))).f (index m a b k)) :
    c ≫ suffixCommonInput m hm F a b k E = c ≫ suffixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (suffix_common_boundary m hm F a b k E hE)
  have hz : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m))).f (index m a b k) ≫
      suffixCommonPrimitive m hm F a b k E = 0 := suffix_common_primitive_diagonal_zero m hm F a b k E
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫ suffixCommonPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, Category.assoc, hz, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

theorem suffix_original_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixOriginalPrimitive m hm F a b k E) =
    NativeRawOriginalScalarReduction.suffixOriginal m hm F a b k E - suffixOrderedInput m hm F a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom ((_ + _) - _) = _
  rw [map_sub, map_add]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawOriginalScalarReduction.suffixPrimitive m hm F a b k E) +
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawStage101Bridge.suffixPrimitive m hm F a b k E) -
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeOrderedScalarPullback.primitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E) = _
  rw [NativeRawOriginalScalarReduction.suffix_boundary m hm F a b k E hE,
    NativeRawStage101Bridge.suffix_boundary m hm F a b k E hE,
    NativeOrderedScalarPullback.original_boundary m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E hE]
  change (_ - _) + (_ - _) - (suffixOrderedInput m hm F a b k E - _) = _
  abel

theorem suffix_original_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) = 0) :
    c ≫ NativeRawOriginalScalarReduction.suffixOriginal m hm F a b k E = c ≫ suffixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (suffix_original_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫ suffixOriginalPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, zero_comp, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.NativeOriginalTwoStageClockComparison
