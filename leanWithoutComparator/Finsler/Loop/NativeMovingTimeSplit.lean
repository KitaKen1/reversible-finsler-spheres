module

public import Finsler.Loop.NativeMovingTriangleSupport
public import Finsler.Loop.NativeGlobalDoublePrismCoefficient

/-! Genuine moving-time additivity on the ORIGINAL rotation input.
The full source-boundary term vanishes by the actual excluded-start
carrier. The interval with constant clocks 0 and 1 is exactly the
old outer time prism, so the operation is never replaced. -/
@[expose] public section
namespace Finsler.NativeMovingTimeSplit
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMovingTriangleSupport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def rotationInput {n : ℕ} (P : Sphere n) (p : ℕ) :=
  (chains (NativeGlobalTimeSquare.source P)).iCycles p ≫
    ((DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.source P)).toSSet.chainComplexMap coeff).hom p (p + 1)

def evaluation (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    (a b : NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :=
  rotationInput P (3 * m) ≫
    MovingTimeTriangleChain.component (cutMap P v₀ k) a b (3 * m + 1) ≫
      GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη

theorem triangle_split (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    (a : Fin 3 → (NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    evaluation m P v₀ k (a 0) (a 2) hρ hρr hr hη =
      evaluation m P v₀ k (a 0) (a 1) hρ hρr hr hη +
      evaluation m P v₀ k (a 1) (a 2) hρ hρr hr hη := by
  have he := congrArg (fun f => rotationInput P (3 * m) ≫ f)
    (MovingTimeTriangleChain.closed_split (cutMap P v₀ k) a (3 * m)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)
      (GlobalCutTimePrismAlignment.parameter_closed m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη))
  have hz := source_boundary_term_zero m P v₀ k a hρ hρr hr hη hη2
  simpa only [evaluation, rotationInput, Preadditive.comp_add, Category.assoc, hz, add_zero] using he

theorem full_component {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (p : ℕ) :
    MovingTimeTriangleChain.component (cutMap P v₀ k)
      (MovingTimeTriangleGeometry.constantClock (NativeGlobalTimeSquare.rotationDomain P) 0)
      (MovingTimeTriangleGeometry.constantClock (NativeGlobalTimeSquare.rotationDomain P) 1) p =
    ((DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)).toSSet.chainComplexMap coeff).hom p (p + 1) ≫
      (push (NativeGlobalTimeSquare.intoCut P v₀ k)).f (p + 1) := by
  have h := congrArg (fun h => h ≫ (push (NativeGlobalTimeSquare.intoCut P v₀ k)).f (p + 1))
    (TimeShuffleComparison.rectangle_eq_prism (DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)) p)
  simpa only [MovingTimeTriangleChain.component, MovingTimeTriangleGeometry.full_segment, Category.id_comp,
    cutMap, push_comp, HomologicalComplex.comp_f, TimeShuffleComparison.rectangle,
    UniversalTimeTriangleChain.interval, Category.assoc] using h

theorem full_evaluation (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    evaluation m P v₀ k
      (MovingTimeTriangleGeometry.constantClock (NativeGlobalTimeSquare.rotationDomain P) 0)
      (MovingTimeTriangleGeometry.constantClock (NativeGlobalTimeSquare.rotationDomain P) 1) hρ hρr hr hη =
    (chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      NativeGlobalDoublePrismCoefficient.cochain m P v₀ k hρ hρr hr hη := by
  simp only [evaluation, full_component, rotationInput, NativeGlobalDoublePrismCoefficient.cochain,
    NativeGlobalTimeSquare.squarePrism, Category.assoc]
  rfl

end
end Finsler.NativeMovingTimeSplit
