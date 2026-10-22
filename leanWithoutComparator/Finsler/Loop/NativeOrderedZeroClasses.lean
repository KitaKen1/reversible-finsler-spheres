module

public import Finsler.Loop.NativeOrderedPairCoordinates
public import Finsler.Loop.DoubleTimeRelativePairing
public import Finsler.Loop.NativeMovingGlobalDecomposition

/-! The original chronological j=4 piece is ZERO for every northern
rotation quarter. Reuse actual zero RELATIVE classes, not merely old
numeric branch values. They kill every changed input, so neither
source-assembly nor time-exchange invariance is needed for these
three pieces. The old global coefficient consequently has nine terms. -/
@[expose] public section
namespace Finsler.NativeOrderedZeroClasses
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMovingThirteen Finsler.NativeMovingOrderedChartAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem forward_class_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) (3 * m + 2)
      (NativeNorthForwardValues.northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8)
      (NativeNorthForwardValues.northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8) = 0 := by
  have hg : NativeGraphBranchPairing.primitiveClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) = 0 := by
    unfold NativeGraphBranchPairing.primitiveClass
    rw [NativeGraphLocalCapReduction.original_graph_class_zero m hm P v₀ b hb hρ hρr hr hη hr8 hη8, map_zero]
  have hn := NativeGraphBranchPairing.primitiveClass_pullback m P v₀ b hρ hρr hr hη (by linarith) (by linarith)
  rw [hg, map_zero] at hn
  exact (NativeNorthForwardValues.northPrimitive_class m P v₀ b hρ hρr hr hη hr8 hη8).trans hn.symm

theorem wrapped_class_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) (3 * m + 2)
      (NativeNorthWrappedValues.northPrimitive m P v₀ 1 hρ hρr hr hη hr8 hη8)
      (NativeNorthWrappedValues.northPrimitive_closed m P v₀ 1 hρ hρr hr hη hr8 hη8) = 0 := by
  have hg : NativeWrappedBranchValues.graphPrimitiveClass m P v₀ 1 hρ hρr hr hη hr8 hη8 = 0 := by
    unfold NativeWrappedBranchValues.graphPrimitiveClass
    rw [NativeWrappedGraphClass.boundary_nonadjacent_zero m hm P v₀ hρ hρr hr hη hr8 hη8, map_zero]
  have hn := NativeWrappedBranchValues.graphPrimitiveClass_pullback m P v₀ 1 hρ hρr hr hη hr8 hη8
  rw [hg, map_zero] at hn
  exact (NativeNorthWrappedValues.northPrimitive_class m P v₀ 1 hρ hρr hr hη hr8 hη8).trans hn.symm

theorem forward_segment_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentEvaluation m P v₀ (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b) hρ hρr hr hη = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hz := DoubleTimeRelativePairing.pairing_zero (NativeGlobalTimeSquare.source P)
    (NativePairBoundaryRelativeCut.pair P v₀) (NativeOrderedPairCoordinates.pairMap P v₀ b true) (3 * m)
    (NativeNorthForwardValues.northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8)
    (NativeNorthForwardValues.northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8)
    (forward_class_zero m hm P v₀ b hb hρ hρr hr hη hr8 hη8) c
  rw [NativeOrderedPairCoordinates.pairMap_fst, NativeNorthForwardValues.northPrimitive_toAmbient] at hz
  change (segmentEvaluation m P v₀ (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b) hρ hρr hr hη).hom c = 0
  rw [NativeMovingSquareChain.segment_square, NativeOrderedPairCoordinates.forward_map, pullback_comp]
  exact hz

theorem wrapped_segment_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentEvaluation m P v₀ 2 4 hρ hρr hr hη = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hz := DoubleTimeRelativePairing.pairing_zero (NativeGlobalTimeSquare.source P)
    (NativePairBoundaryRelativeCut.pair P v₀) (NativeOrderedPairCoordinates.pairMap P v₀ 1 false) (3 * m)
    (NativeNorthWrappedValues.northPrimitive m P v₀ 1 hρ hρr hr hη hr8 hη8)
    (NativeNorthWrappedValues.northPrimitive_closed m P v₀ 1 hρ hρr hr hη hr8 hη8)
    (wrapped_class_zero m hm P v₀ hρ hρr hr hη hr8 hη8) c
  rw [NativeOrderedPairCoordinates.pairMap_fst, NativeNorthWrappedValues.northPrimitive_toAmbient] at hz
  change (segmentEvaluation m P v₀ 2 4 hρ hρr hr hη).hom c = 0
  rw [NativeMovingSquareChain.segment_square]
  have he := NativeOrderedPairCoordinates.wrapped_map P v₀ 1
  change assembledCoordinates P 0 ≫ NativeMovingNonnorthGeometry.segmentFamily P v₀ 2 4 = _ at he
  rw [he, pullback_comp]
  exact hz

theorem first_target_segments_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    segmentEvaluation m P v₀ k 4 hρ hρr hr hη = 0 := by
  fin_cases k
  · exact forward_segment_zero m hm P v₀ 0 (by decide) hρ hρr hr hη hr8 hη8
  · exact forward_segment_zero m hm P v₀ 2 (by decide) hρ hρr hr hη hr8 hη8
  · exact wrapped_segment_zero m hm P v₀ hρ hρr hr hη hr8 hη8

theorem north_three (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      NativeGlobalDoublePrismCoefficient.cochain m P v₀ k hρ hρr hr hη =
      segmentEvaluation m P v₀ k 0 hρ hρr hr hη + segmentEvaluation m P v₀ k 8 hρ hρr hr hη +
      segmentEvaluation m P v₀ k 12 hρ hρr hr hη := by
  have h := NativeMovingNonnorthZero.north_four m P v₀ k hρ hρr hr hη (by linarith) (by linarith)
  rw [first_target_segments_zero m hm P v₀ k hρ hρr hr hη hr8 hη8, add_zero] at h
  exact h

theorem coefficient_nine (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ = ∑ k : Fin 3,
      (NativeMovingGlobalDecomposition.segmentScalar m hm P v₀ k 0 hρ hρr hr hη +
       NativeMovingGlobalDecomposition.segmentScalar m hm P v₀ k 8 hρ hρr hr hη +
       NativeMovingGlobalDecomposition.segmentScalar m hm P v₀ k 12 hρ hρr hr hη) := by
  rw [NativeGlobalDoublePrismCoefficient.original_coefficient_raw m hm P v₀ hρ hρr hr hη (by linarith)]
  simp_rw [north_three m hm P v₀ _ hρ hρr hr hη hr8 hη8]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_add, LinearMap.add_apply,
    NativeMovingGlobalDecomposition.segmentScalar]

end
end Finsler.NativeOrderedZeroClasses
