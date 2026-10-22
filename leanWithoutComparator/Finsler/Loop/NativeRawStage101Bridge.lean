module

public import Finsler.Loop.NativeRawReindexedComparison
public import Finsler.Loop.NativeRawClockScalarComparison

/-! BOTH actual raw cup reductions connect to the SAME Stage101
inverse-image common input. All cup-one, reindexed subdivision and
inverse-image subdivision terms are retained. Their sum vanishes on
the full inverse diagonal and gives genuine relative-chain equality. -/
@[expose] public section
namespace Finsler.NativeRawStage101Bridge
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockSupportedAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem pullback_primitive_diagonal_zero {X : TopCat.{0}} (f : X ⟶ NativeOrderedDoubleCapCommon.source m) :
    cochainPullback (SupportedCap.subspaceMap X (f ⁻¹' NativeOrderedDoubleCutSupported.diagonal m)) (index m a b k)
      (NativeOrderedScalarPullback.pullbackPrimitive m hm F f a b k E) = 0 :=
  MultiFarPreimagePullback.primitive_zero f (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
    (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
    (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
    (NativeOrderedDoubleCapCommon.test m hm F a b k E)
    (NativeOrderedDoubleCutSupported.diagonal m) (NativeOrderedDoubleCapCommon.diagonal_test_zero m hm F a b k E)

def prefixPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  NativeRawCupOrder.prefixPrimitive m hm F a b k E +
    NativeRawReindexedComparison.prefixPrimitive m hm F a b k E -
    NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixPrimitive m hm F a b k E) =
    NativeRawDoubleCapCommon.prefixCoupled m hm F a b k E -
      NativeOrderedScalarPullback.localValue m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom (_ - _) = _
  rw [map_sub, map_add]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawCupOrder.prefixPrimitive m hm F a b k E) +
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawReindexedComparison.prefixPrimitive m hm F a b k E) -
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E) = _
  rw [NativeRawCupOrder.prefix_boundary m hm F a b k E hE, NativeRawReindexedComparison.prefix_boundary m hm F a b k E hE,
    NativeOrderedScalarPullback.local_boundary m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E hE]
  abel

theorem prefix_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
    (prefixPrimitive m hm F a b k E) = 0 := by
  have hz : cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m))
      (index m a b k) (NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E) = 0 :=
    pullback_primitive_diagonal_zero m hm F a b k E (NativeRawClockMaps.prefixClock (m + 1))
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)).op).f (index m a b k)).hom (_ - _) = 0
  rw [map_sub, map_add]
  change cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
      (NativeRawCupOrder.prefixPrimitive m hm F a b k E) +
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
      (NativeRawReindexedComparison.prefixPrimitive m hm F a b k E) -
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
      (NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E) = 0
  rw [NativeRawCupOrder.prefix_primitive_diagonal_zero, NativeRawReindexedComparison.prefix_primitive_diagonal_zero,
    hz]
  rw [add_zero, sub_self]

theorem prefix_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (NativeRawDoubleCapCommon.prefixDiagonal m))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m))).f (index m a b k)) :
    c ≫ NativeRawDoubleCapCommon.prefixCoupled m hm F a b k E =
    c ≫ NativeOrderedScalarPullback.localValue m hm F (NativeRawClockMaps.prefixClock (m + 1)) a b k E := by
  have hb := congrArg (fun T => c ≫ T) (prefix_boundary m hm F a b k E hE)
  have hz : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m))).f (index m a b k) ≫
      prefixPrimitive m hm F a b k E = 0 := prefix_primitive_diagonal_zero m hm F a b k E
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫ prefixPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, Category.assoc, hz, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

def suffixPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  NativeRawReindexedComparison.suffixPrimitive m hm F a b k E -
    NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixPrimitive m hm F a b k E) =
    NativeRawDoubleCapCommon.suffixCoupled m hm F a b k E -
      NativeOrderedScalarPullback.localValue m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom (_ - _) = _
  rw [map_sub]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (NativeRawReindexedComparison.suffixPrimitive m hm F a b k E) -
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E) = _
  rw [NativeRawReindexedComparison.suffix_boundary m hm F a b k E hE,
    NativeOrderedScalarPullback.local_boundary m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E hE]
  abel

theorem suffix_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
    (suffixPrimitive m hm F a b k E) = 0 := by
  have hz : cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m))
      (index m a b k) (NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E) = 0 :=
    pullback_primitive_diagonal_zero m hm F a b k E (NativeRawClockMaps.suffixClock (m + 1))
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)).op).f (index m a b k)).hom (_ - _) = 0
  rw [map_sub]
  change cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
      (NativeRawReindexedComparison.suffixPrimitive m hm F a b k E) -
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
      (NativeOrderedScalarPullback.pullbackPrimitive m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E) = 0
  rw [NativeRawReindexedComparison.suffix_primitive_diagonal_zero,
    hz]
  exact sub_self 0

theorem suffix_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (NativeRawDoubleCapCommon.suffixDiagonal m))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m))).f (index m a b k)) :
    c ≫ NativeRawDoubleCapCommon.suffixCoupled m hm F a b k E =
    c ≫ NativeOrderedScalarPullback.localValue m hm F (NativeRawClockMaps.suffixClock (m + 1)) a b k E := by
  have hb := congrArg (fun T => c ≫ T) (suffix_boundary m hm F a b k E hE)
  have hz : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m))).f (index m a b k) ≫
      suffixPrimitive m hm F a b k E = 0 := suffix_primitive_diagonal_zero m hm F a b k E
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫ suffixPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, Category.assoc, hz, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.NativeRawStage101Bridge
