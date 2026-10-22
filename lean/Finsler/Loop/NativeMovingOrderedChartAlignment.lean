module

public import Finsler.Loop.NativeMovingNonnorthZero
public import Finsler.Loop.NativeNorthForwardSquare
public import Finsler.Loop.NativeNorthWrappedSquare

/-! Exact coordinate comparison of all SIX chronological distinct-leg
segments with the already evaluated old native cells. The source
assembly is EXPLICIT. Forward cells also require an EXPLICIT exchange
of the two time coordinates; wrapped cells do not. These are map
identities only, never an assumed invariance of the prism input. -/
@[expose] public section
namespace Finsler.NativeMovingOrderedChartAlignment
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.MeridianTripleQuarterClocks Finsler.NativeMovingNonnorthGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1600000

def assembledCoordinates {n : ℕ} (P : Sphere n) (b : Fin 3) :
    NativeGlobalTimeSquare.squareDomain P ⟶ NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I :=
  TopCat.ofHom ⟨fun z => ((z.2.1,
    NativeMeridianPairCoordinates.assembly b z.2.2.1.1 z.2.2.1.2 z.2.2.2), ULift.up z.1), by
      fin_cases b <;> dsimp [NativeMeridianPairCoordinates.assembly] <;> fun_prop⟩

def timeSwap {n : ℕ} (P : Sphere n) :
    NativeGlobalTimeSquare.squareDomain P ⟶ NativeGlobalTimeSquare.squareDomain P :=
  TopCat.ofHom ⟨fun z => (z.2.1, (z.1, z.2.2)), by fun_prop⟩

def forwardSegment (b : Fin 3) : Fin 13 := if b = 1 then 8 else 4
def wrappedSegment (b : Fin 3) : Fin 13 := if b = 1 then 4 else 8

theorem forward_map {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    assembledCoordinates P b ≫ segmentFamily P v₀ (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b) =
      timeSwap P ≫ (NativeNorthForwardSquare.cell P b ≫
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
      NativeNorthCutClocks.targetEnds, clock, localTime] <;> ring
  · rfl

theorem wrapped_map {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    assembledCoordinates P b ≫ segmentFamily P v₀ (NativeMeridianMatchingLoci.pairRight b) (wrappedSegment b) =
      NativeNorthWrappedSquare.cell P b ≫
        NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b) := by
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
      NativeNorthCutClocks.targetEnds, clock, localTime] <;> ring
  · rfl

theorem forward_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    cochainPullback (assembledCoordinates P b ≫
      segmentFamily P v₀ (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b)) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) =
    cochainPullback (timeSwap P ≫ (NativeNorthForwardSquare.cell P b ≫
      NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b))) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) :=
  congrArg (fun f => cochainPullback f (3 * m + 2)
    (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη))
    (forward_map P v₀ b)

theorem wrapped_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    cochainPullback (assembledCoordinates P b ≫
      segmentFamily P v₀ (NativeMeridianMatchingLoci.pairRight b) (wrappedSegment b)) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) =
    cochainPullback (NativeNorthWrappedSquare.cell P b ≫
      NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b)) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) :=
  congrArg (fun f => cochainPullback f (3 * m + 2)
    (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη))
    (wrapped_map P v₀ b)

end
end Finsler.NativeMovingOrderedChartAlignment
