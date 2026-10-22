module

public import Finsler.Loop.NativeMovingOrderedChartAlignment

/-! Relate an ACTUAL chronological segment to the SAME original
double prism. The identity assembly gives the actual wrapped 01
term value ONE immediately, without a source-permutation or time-swap
invariance assumption. Other source/time transports remain separate. -/
@[expose] public section
namespace Finsler.NativeMovingSquareChain
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMovingTriangleSupport Finsler.NativeMovingNonnorthGeometry
open Finsler.NativeMovingOrderedChartAlignment Finsler.NativeMovingThirteen
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem unpack_family {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (j : Fin 13) :
    (DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)).h ≫
      (assembledCoordinates P 0 ≫ segmentFamily P v₀ k j) = segmentFamily P v₀ k j := by
  apply TopCat.ext
  intro z
  rfl

theorem segment_component {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (j : Fin 13) (p : ℕ) :
    MovingTimeTriangleChain.component (cutMap P v₀ k)
      (NativeNorthCutClocks.breakClock P k j.castSucc) (NativeNorthCutClocks.breakClock P k j.succ) p =
    ((DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)).toSSet.chainComplexMap coeff).hom p (p + 1) ≫
      (push (assembledCoordinates P 0 ≫ segmentFamily P v₀ k j)).f (p + 1) := by
  have h := congrArg (fun h => h ≫ (push (assembledCoordinates P 0 ≫ segmentFamily P v₀ k j)).f (p + 1))
    (TimeShuffleComparison.rectangle_eq_prism
      (DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)) p)
  have hm := congrArg (fun f => (push f).f (p + 1)) (unpack_family P v₀ k j)
  calc
    _ = UniversalTimeTriangleChain.interval (NativeGlobalTimeSquare.rotationDomain P) p ≫
        (push (segmentFamily P v₀ k j)).f (p + 1) := rfl
    _ = UniversalTimeTriangleChain.interval (NativeGlobalTimeSquare.rotationDomain P) p ≫
        (push ((DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)).h ≫
          (assembledCoordinates P 0 ≫ segmentFamily P v₀ k j))).f (p + 1) :=
      congrArg (fun f => UniversalTimeTriangleChain.interval (NativeGlobalTimeSquare.rotationDomain P) p ≫ f) hm.symm
    _ = TimeShuffleComparison.rectangle (DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)) p ≫
        (push (assembledCoordinates P 0 ≫ segmentFamily P v₀ k j)).f (p + 1) := by
      simp only [TimeShuffleComparison.rectangle, UniversalTimeTriangleChain.interval,
        push_comp, HomologicalComplex.comp_f, Category.assoc]
    _ = _ := h

theorem segment_square (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (j : Fin 13) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    segmentEvaluation m P v₀ k j hρ hρr hr hη =
    (chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      NativeGlobalTimeSquare.squarePrism (NativeGlobalTimeSquare.source P) (3 * m) ≫
      cochainPullback (assembledCoordinates P 0 ≫ segmentFamily P v₀ k j) (3 * m + 2)
        (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) := by
  simp only [segmentEvaluation, NativeMovingTimeSplit.evaluation, segment_component,
    NativeMovingTimeSplit.rotationInput, NativeGlobalTimeSquare.squarePrism, Category.assoc]
  rfl

theorem original_wrapped_01_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (segmentEvaluation m P v₀ 1 8 hρ hρr hr hη).hom
      (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) = 1 := by
  rw [segment_square]
  have he : assembledCoordinates P 0 ≫ segmentFamily P v₀ 1 8 =
      NativeNorthWrappedSquare.cell P 0 ≫ NativeGlobalTimeSquare.intoCut P v₀ 1 := wrapped_map P v₀ 0
  rw [he]
  exact NativeNorthWrappedSquare.cell_value m hm P v₀ 0 hρ hρr hr hη hr8 hη8

end
end Finsler.NativeMovingSquareChain
