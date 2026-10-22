module

public import Finsler.Loop.NativeMovingNonnorthGeometry

/-! Exact geometry of the SIX remaining partial same-leg pieces.
Both cut endpoints run along the SAME original meridian direction:
short piece from s to s+(1-s)t, long complement from st to s after
one true circle period. This keeps both seam pieces and identifies
the common diagonal needed for a genuine supported-cap comparison. -/
@[expose] public section
namespace Finsler.NativeSameLegClockGeometry
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.MeridianTripleQuarterClocks Finsler.NativeMovingTriangleSupport
open Finsler.NativeMovingNonnorthGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def later (s t : ClosedInterval) : ClosedInterval :=
  ⟨(s : ℝ) + (1 - (s : ℝ)) * (t : ℝ), by
    constructor
    · nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
    · nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]⟩

def earlier (s t : ClosedInterval) : ClosedInterval :=
  ⟨(s : ℝ) * (t : ℝ), ⟨mul_nonneg s.property.1 t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 s.property.1).trans (by simpa using s.property.2)⟩⟩

theorem short_clock (k : Fin 3) (s t : ClosedInterval) :
    clock k 0 s +
      ((1 - (t : ℝ)) * (NativeNorthCutClocks.breakTime k 0 s : ℝ) +
        (t : ℝ) * (NativeNorthCutClocks.breakTime k 1 s : ℝ)) = clock k 0 (later s t) := by
  fin_cases k <;> norm_num [NativeNorthCutClocks.breakTime, NativeNorthCutClocks.breakValue,
    NativeNorthCutClocks.targetEnds, clock, localTime, later] <;> ring

theorem long_clock (k : Fin 3) (s t : ClosedInterval) :
    clock k 0 s +
      ((1 - (t : ℝ)) * (NativeNorthCutClocks.breakTime k 12 s : ℝ) +
        (t : ℝ) * (NativeNorthCutClocks.breakTime k 13 s : ℝ)) = clock k 0 (earlier s t) + 1 := by
  fin_cases k <;> norm_num [NativeNorthCutClocks.breakTime, NativeNorthCutClocks.breakValue,
    NativeNorthCutClocks.targetEnds, clock, localTime, earlier] <;> ring

theorem short_endpoint {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    (z : NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I) :
    H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 0 z) =
      piece P v₀ (NativeTripleSelfEvaluation.directions z.1.2 k) 0 (later z.1.1 z.2.down) := by
  rw [endpoint_segment, ← AddCircle.coe_add]
  have h := congrArg (fun u : ℝ => SobolevCircleRepresentative.sphereCircleMap
    (NativeH1TripleMeridian.native P v₀ z.1.2) (u : SobolevCircleRepresentative.Circle))
    (short_clock k z.1.1 z.2.down)
  exact h.trans (NativeTripleSelfEvaluation.circle_quarter P v₀ z.1.2 k 0 (later z.1.1 z.2.down))

theorem long_endpoint {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    (z : NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I) :
    H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 12 z) =
      piece P v₀ (NativeTripleSelfEvaluation.directions z.1.2 k) 0 (earlier z.1.1 z.2.down) := by
  rw [endpoint_segment, ← AddCircle.coe_add]
  have h := congrArg (fun u : ℝ => SobolevCircleRepresentative.sphereCircleMap
    (NativeH1TripleMeridian.native P v₀ z.1.2) (u : SobolevCircleRepresentative.Circle))
    (long_clock k z.1.1 z.2.down)
  have hp := AddCircle.coe_add_period (1 : ℝ) (clock k 0 (earlier z.1.1 z.2.down))
  exact h.trans ((congrArg (SobolevCircleRepresentative.sphereCircleMap
    (NativeH1TripleMeridian.native P v₀ z.1.2)) hp).trans
      (NativeTripleSelfEvaluation.circle_quarter P v₀ z.1.2 k 0 (earlier z.1.1 z.2.down)))

theorem later_ge (s t : ClosedInterval) : (s : ℝ) ≤ (later s t : ℝ) := by
  change (s : ℝ) ≤ (s : ℝ) + (1 - (s : ℝ)) * (t : ℝ)
  nlinarith [s.property.2, t.property.1]

theorem earlier_le (s t : ClosedInterval) : (earlier s t : ℝ) ≤ (s : ℝ) := by
  exact (mul_le_mul_of_nonneg_left t.property.2 s.property.1).trans (by simp)

theorem short_diagonal (s : ClosedInterval) : later s 0 = s := by apply Subtype.ext; simp [later]
theorem long_diagonal (s : ClosedInterval) : earlier s 1 = s := by apply Subtype.ext; simp [earlier]

end
end Finsler.NativeSameLegClockGeometry
