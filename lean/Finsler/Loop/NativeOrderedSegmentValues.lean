module

public import Finsler.Loop.NativeOrderedProductScalars
public import Finsler.Loop.NativeOrderedZeroClasses
public import Finsler.Loop.NativeMovingSquareChain

/-! Connect the two remaining chronological target pieces to their
actual relative classes and original double-time inputs. All three
j=8 scalars are ONE. The same-leg pieces remain explicit obligations. -/
@[expose] public section
namespace Finsler.NativeOrderedSegmentValues
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativePairRelativeSphereTransport Finsler.NativeOrderedPairClosing
open Finsler.NativeMovingThirteen Finsler.NativeMovingOrderedChartAlignment Finsler.NativeMovingGlobalDecomposition
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem native_graph_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (b : Fin 3) (forward : Bool) (a : RelativeCup.cohomology (graphPair P v₀) (3 * m + 2)) :
    RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (nativeToGraph P v₀) (3 * m + 2)).hom a)
      (nativeInput m hm P v₀ b forward) =
      RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a (graphInput m hm P v₀ b forward) := by
  have he := congrArg (fun φ => φ (nativeInput m hm P v₀ b forward))
    (RelativeKronecker.naturality (nativeToGraph P v₀) (3 * m + 2) a)
  change _ = RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a
    ((TopPair.singularHomologyMap (nativeToGraph P v₀) coeff (3 * m + 2)).hom
      (nativeInput m hm P v₀ b forward)) at he
  exact he.trans (congrArg (RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a)
    (nativeInput_image m hm P v₀ b forward))

theorem projection_pairing (Q : TopPair.{0}) (q : ℕ) (a : RelativeCup.cohomology Q q)
    (x : homologyZMod2 Q.fst q) :
    RelativeKronecker.comparison Q q a ((Q.singularHomologyπ coeff q).hom x) =
      (kroneckerMap Q.fst q).hom ((relativeToPool Q q).hom a) x :=
  congrArg (fun φ => φ x) (RelativeKronecker.fromRelative_comparison Q q a)

theorem forward_segment_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentScalar m hm P v₀ (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b) hρ hρr hr hη =
      RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2)
        (NativeGraphBranchPairing.primitiveClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith))
        (graphInput m hm P v₀ b true) := by
  have he := DoubleTimeRelativePairing.pairing (NativeGlobalTimeSquare.source P)
    (NativePairBoundaryRelativeCut.pair P v₀) (NativeOrderedPairCoordinates.pairMap P v₀ b true) (3 * m)
    (NativeNorthForwardValues.northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8)
    (NativeNorthForwardValues.northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8)
    (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)
  rw [NativeOrderedPairCoordinates.pairMap_fst, NativeNorthForwardValues.northPrimitive_toAmbient,
    NativeNorthForwardValues.northPrimitive_class, ← NativeGraphBranchPairing.primitiveClass_pullback,
    NativeThetaCoefficientSixQuarters.sourceCycle_class] at he
  change RelativeKronecker.comparison _ _ _ (nativeInput m hm P v₀ b true) = _ at he
  rw [native_graph_pairing] at he
  unfold segmentScalar
  rw [NativeMovingSquareChain.segment_square, NativeOrderedPairCoordinates.forward_map, pullback_comp]
  exact he.symm

theorem wrapped_segment_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentScalar m hm P v₀ (NativeMeridianMatchingLoci.pairRight b) (wrappedSegment b) hρ hρr hr hη =
      RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2)
        (NativeWrappedBranchValues.graphPrimitiveClass m P v₀ b hρ hρr hr hη hr8 hη8)
        (graphInput m hm P v₀ b false) := by
  have he := DoubleTimeRelativePairing.pairing (NativeGlobalTimeSquare.source P)
    (NativePairBoundaryRelativeCut.pair P v₀) (NativeOrderedPairCoordinates.pairMap P v₀ b false) (3 * m)
    (NativeNorthWrappedValues.northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8)
    (NativeNorthWrappedValues.northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8)
    (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)
  rw [NativeOrderedPairCoordinates.pairMap_fst, NativeNorthWrappedValues.northPrimitive_toAmbient,
    NativeNorthWrappedValues.northPrimitive_class, ← NativeWrappedBranchValues.graphPrimitiveClass_pullback,
    NativeThetaCoefficientSixQuarters.sourceCycle_class] at he
  change RelativeKronecker.comparison _ _ _ (nativeInput m hm P v₀ b false) = _ at he
  rw [native_graph_pairing] at he
  unfold segmentScalar
  rw [NativeMovingSquareChain.segment_square, NativeOrderedPairCoordinates.wrapped_map, pullback_comp]
  exact he.symm

theorem original_forward02_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentScalar m hm P v₀ 0 8 hρ hρr hr hη = 1 := by
  have he := forward_segment_pairing m hm P v₀ 1 hρ hρr hr hη hr8 hη8
  rw [NativeOrderedProductProjection.graph02_projection, projection_pairing] at he
  change _ = (kroneckerMap (graphSpace P) (3 * m + 2)).hom
    (NativeGraphBranchPairing.absoluteClass m P v₀ 1 hρ hρr hr hη (by linarith) (by linarith)) _ at he
  rw [NativeExplicitGraphClass.original_absolute_class m hm P v₀ hρ hρr hr hη hr8 hη8,
    NativeOrderedProductScalars.scalar02_one] at he
  exact he

theorem original_wrapped12_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentScalar m hm P v₀ 2 8 hρ hρr hr hη = 1 := by
  have he := wrapped_segment_pairing m hm P v₀ 2 hρ hρr hr hη hr8 hη8
  rw [NativeOrderedProductProjection.graph12_projection, projection_pairing] at he
  change _ = (kroneckerMap (graphSpace P) (3 * m + 2)).hom
    (NativeWrappedBranchValues.absoluteClass m P v₀ 2 hρ hρr hr hη hr8 hη8) _ at he
  rw [NativeWrappedBranchValues.absolute_adjacent m hm P v₀ 2 (by decide) hρ hρr hr hη hr8 hη8,
    NativeOrderedProductScalars.scalar12_one] at he
  exact he

theorem last_target_segments_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentScalar m hm P v₀ k 8 hρ hρr hr hη = 1 := by
  fin_cases k
  · exact original_forward02_one m hm P v₀ hρ hρr hr hη hr8 hη8
  · exact NativeMovingSquareChain.original_wrapped_01_one m hm P v₀ hρ hρr hr hη hr8 hη8
  · exact original_wrapped12_one m hm P v₀ hρ hρr hr hη hr8 hη8

end
end Finsler.NativeOrderedSegmentValues
