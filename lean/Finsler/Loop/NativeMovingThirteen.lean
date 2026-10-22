module

public import Finsler.Loop.NativeMovingTimeSplit
public import Finsler.Loop.NativeNorthCutClocks
public import Finsler.Loop.FiniteClockTelescope

/-! Decompose EACH original northern double prism into all THIRTEEN
chronological moving cut intervals, on the SAME original source cycle
and original parameter cochain. Endpoint and source-boundary terms
are proved, not discarded. No source permutation or vanishing of the
same-leg/excluded pieces is assumed by this decomposition. -/
@[expose] public section
namespace Finsler.NativeMovingThirteen
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMovingTimeSplit
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem first_clock {n : ℕ} (P : Sphere n) (k : Fin 3) :
    NativeNorthCutClocks.breakClock P k 0 =
      MovingTimeTriangleGeometry.constantClock (NativeGlobalTimeSquare.rotationDomain P) 0 := by
  apply TopCat.ext
  intro z
  apply ULift.ext
  exact NativeNorthCutClocks.break_zero k z.1

theorem last_clock {n : ℕ} (P : Sphere n) (k : Fin 3) :
    NativeNorthCutClocks.breakClock P k 13 =
      MovingTimeTriangleGeometry.constantClock (NativeGlobalTimeSquare.rotationDomain P) 1 := by
  apply TopCat.ext
  intro z
  apply ULift.ext
  exact NativeNorthCutClocks.break_one k z.1

def segmentEvaluation (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (j : Fin 13) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :=
  evaluation m P v₀ k (NativeNorthCutClocks.breakClock P k j.castSucc)
    (NativeNorthCutClocks.breakClock P k j.succ) hρ hρr hr hη

theorem north_thirteen (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    (chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      NativeGlobalDoublePrismCoefficient.cochain m P v₀ k hρ hρr hr hη =
    ∑ j : Fin 13, segmentEvaluation m P v₀ k j hρ hρr hr hη := by
  have hE (a b c : NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I) :
      evaluation m P v₀ k a c hρ hρr hr hη =
        evaluation m P v₀ k a b hρ hρr hr hη + evaluation m P v₀ k b c hρ hρr hr hη :=
    triangle_split m P v₀ k ![a, b, c] hρ hρr hr hη hη2
  have h := FiniteClockTelescope.additive_paths
    (fun a b => evaluation m P v₀ k a b hρ hρr hr hη) hE 13 (NativeNorthCutClocks.breakClock P k)
  simpa only [show Fin.last 13 = (13 : Fin 14) from rfl, first_clock, last_clock,
    full_evaluation, segmentEvaluation] using h

theorem coefficient_thirtynine (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      ∑ k : Fin 3, ∑ j : Fin 13,
        (segmentEvaluation m P v₀ k j hρ hρr hr hη).hom
          (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) := by
  rw [NativeGlobalDoublePrismCoefficient.original_coefficient_raw m hm P v₀ hρ hρr hr hη hη2]
  simp_rw [north_thirteen m P v₀ _ hρ hρr hr hη hη2]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]

end
end Finsler.NativeMovingThirteen
