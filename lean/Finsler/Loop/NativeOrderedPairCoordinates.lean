module

public import Finsler.Loop.NativeMovingSquareChain
public import Finsler.Loop.NativeNorthForwardValues
public import Finsler.Loop.NativeNorthWrappedValues

/-! Coordinates for the chronological ordered cells on the ORIGINAL
source. The source directions are read in their true positions;
the source fundamental class is never declared permutation-invariant.
Both time orders carry all four time faces into the actual native pair. -/
@[expose] public section
namespace Finsler.NativeOrderedPairCoordinates
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMovingNonnorthGeometry Finsler.NativeMovingOrderedChartAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1600000

def sourceOrder {n : ℕ} {P : Sphere n} (b : Fin 3) (z : NativeH1TripleMeridian.parameters P) :
    NativeH1TripleMeridian.parameters P :=
  match b with
  | 0 => z
  | 1 => ((z.1.1, z.2), z.1.2)
  | 2 => ((z.1.2, z.2), z.1.1)

theorem assembly_sourceOrder {n : ℕ} {P : Sphere n} (b : Fin 3) (z : NativeH1TripleMeridian.parameters P) :
    NativeMeridianPairCoordinates.assembly b (sourceOrder b z).1.1 (sourceOrder b z).1.2 (sourceOrder b z).2 = z := by
  fin_cases b <;> rfl

def coordinates {n : ℕ} (P : Sphere n) (b : Fin 3) (forward : Bool) :
    NativeGlobalTimeSquare.squareDomain P ⟶ NativeMeridianPairCoordinates.parameters P :=
  TopCat.ofHom ⟨fun z =>
    ((if forward then z.2.1 else z.1, (sourceOrder b z.2.2).1.1),
      ((if forward then z.1 else z.2.1, (sourceOrder b z.2.2).1.2), (sourceOrder b z.2.2).2)), by
    cases forward <;> fin_cases b <;> dsimp [sourceOrder] <;> fun_prop⟩

theorem faces {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    Set.MapsTo (coordinates P b forward)
      (DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P))
      (NativePairBoundaryRelativeCut.bad P v₀) := by
  intro z hz
  cases forward
  · change z.1 = 0 ∨ z.1 = 1 ∨ z.2.1 = 0 ∨ z.2.1 = 1 ∨ _ ∨ _
    rcases hz with (h | h) | (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · change z.2.1 = 0 ∨ z.2.1 = 1 ∨ z.1 = 0 ∨ z.1 = 1 ∨ _ ∨ _
    rcases hz with (h | h) | (h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

def pairMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    DoubleRelativeTimeCylinder.squarePair (NativeGlobalTimeSquare.source P) ⟶
      NativePairBoundaryRelativeCut.pair P v₀ :=
  TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P))
    (B' := NativePairBoundaryRelativeCut.bad P v₀) (coordinates P b forward) (faces P v₀ b forward)

theorem pairMap_fst {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    TopPair.Hom.fst (pairMap P v₀ b forward) = coordinates P b forward := by
  apply TopCat.ext
  intro z
  exact TopPair.ofSubsetMap_fst_apply (B := DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P))
    (B' := NativePairBoundaryRelativeCut.bad P v₀) (coordinates P b forward) (faces P v₀ b forward) z

theorem forward_map {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    assembledCoordinates P 0 ≫ segmentFamily P v₀ (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b) =
      coordinates P b true ≫ (NativeNorthOrderedCharts.forward P b ≫
        NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b)) := by
  apply TopCat.ext
  intro z
  apply Prod.ext
  · apply Subtype.ext
    change (1 - (z.1 : ℝ)) *
        (NativeNorthCutClocks.breakTime (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b).castSucc z.2.1 : ℝ) +
      (z.1 : ℝ) *
        (NativeNorthCutClocks.breakTime (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b).succ z.2.1 : ℝ) =
      (NativeMeridianPairCoordinates.pairCutTime b (MeridianQuarterIncidence.northTime z.2.1)
        (MeridianQuarterIncidence.northTime z.1) : ℝ)
    fin_cases b <;> norm_num [forwardSegment, NativeMeridianMatchingLoci.pairLeft,
      NativeMeridianMatchingLoci.pairRight, NativeMeridianPairCoordinates.pairCutTime,
      NativeMeridianMatchingLoci.legClock, MeridianQuarterIncidence.northTime,
      NativeNorthCutClocks.breakTime, NativeNorthCutClocks.breakValue,
      NativeNorthCutClocks.targetEnds, MeridianTripleQuarterClocks.clock, MeridianTripleQuarterClocks.localTime] <;> ring
  · change SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀ z.2.2)
        (MeridianTripleQuarterClocks.clock (NativeMeridianMatchingLoci.pairLeft b) 0 z.2.1) =
      SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀
        (NativeMeridianPairCoordinates.assembly b (sourceOrder b z.2.2).1.1
          (sourceOrder b z.2.2).1.2 (sourceOrder b z.2.2).2))
        (MeridianTripleQuarterClocks.clock (NativeMeridianMatchingLoci.pairLeft b) 0 z.2.1)
    rw [assembly_sourceOrder]

theorem wrapped_map {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    assembledCoordinates P 0 ≫ segmentFamily P v₀ (NativeMeridianMatchingLoci.pairRight b) (wrappedSegment b) =
      coordinates P b false ≫ (NativeNorthOrderedCharts.wrapped P b ≫
        NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b)) := by
  apply TopCat.ext
  intro z
  apply Prod.ext
  · apply Subtype.ext
    change (1 - (z.1 : ℝ)) *
        (NativeNorthCutClocks.breakTime (NativeMeridianMatchingLoci.pairRight b) (wrappedSegment b).castSucc z.2.1 : ℝ) +
      (z.1 : ℝ) *
        (NativeNorthCutClocks.breakTime (NativeMeridianMatchingLoci.pairRight b) (wrappedSegment b).succ z.2.1 : ℝ) =
      1 - (NativeMeridianPairCoordinates.pairCutTime b (MeridianQuarterIncidence.northTime z.1)
        (MeridianQuarterIncidence.northTime z.2.1) : ℝ)
    fin_cases b <;> norm_num [wrappedSegment, NativeMeridianMatchingLoci.pairLeft,
      NativeMeridianMatchingLoci.pairRight, NativeMeridianPairCoordinates.pairCutTime,
      NativeMeridianMatchingLoci.legClock, MeridianQuarterIncidence.northTime,
      NativeNorthCutClocks.breakTime, NativeNorthCutClocks.breakValue,
      NativeNorthCutClocks.targetEnds, MeridianTripleQuarterClocks.clock, MeridianTripleQuarterClocks.localTime] <;> ring
  · change SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀ z.2.2)
        (MeridianTripleQuarterClocks.clock (NativeMeridianMatchingLoci.pairRight b) 0 z.2.1) =
      SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀
        (NativeMeridianPairCoordinates.assembly b (sourceOrder b z.2.2).1.1
          (sourceOrder b z.2.2).1.2 (sourceOrder b z.2.2).2))
        (MeridianTripleQuarterClocks.clock (NativeMeridianMatchingLoci.pairRight b) 0 z.2.1)
    rw [assembly_sourceOrder]

end
end Finsler.NativeOrderedPairCoordinates
