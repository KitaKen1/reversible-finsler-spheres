module

public import Finsler.Loop.NativeMovingThirteen

/-! Exact endpoints of all NINE non-northern chronological cut
segments, including wraparound by one period. Their cut endpoints
lie in the existing excluded carrier, with no simplex-wise guess or
discarded seam. The geometric computation is reduced to 27 rational
clock identities before touching the genuine H1 loop map. -/
@[expose] public section
namespace Finsler.NativeMovingNonnorthGeometry
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.MeridianTripleQuarterClocks Finsler.NativeMovingTriangleSupport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1700000

def nonnorthSegment (i q : Fin 3) : Fin 13 := ⟨4 * i.val + q.val + 1, by omega⟩
def targetLeg (k i : Fin 3) : Fin 3 := ⟨(k.val + i.val) % 3, Nat.mod_lt _ (by decide)⟩
def targetTurn (k i : Fin 3) : ℝ := if 3 ≤ k.val + i.val then 1 else 0

theorem target_clock (k i q : Fin 3) (s t : _root_.unitInterval) :
    clock k 0 s +
      ((1 - (t : ℝ)) * (NativeNorthCutClocks.breakTime k (nonnorthSegment i q).castSucc s : ℝ) +
        (t : ℝ) * (NativeNorthCutClocks.breakTime k (nonnorthSegment i q).succ s : ℝ)) =
      clock (targetLeg k i) (NorthRotationPrismLocalization.nonNorthQuarter q) t + targetTurn k i := by
  fin_cases k <;> fin_cases i <;> fin_cases q <;>
    norm_num [nonnorthSegment, targetLeg, targetTurn, NativeNorthCutClocks.breakTime,
      NativeNorthCutClocks.breakValue, NativeNorthCutClocks.targetEnds,
      NorthRotationPrismLocalization.nonNorthQuarter, clock, localTime] <;> ring

theorem turn_period (k i : Fin 3) (u : ℝ) :
    ((u + targetTurn k i : ℝ) : SobolevCircleRepresentative.Circle) =
      (u : SobolevCircleRepresentative.Circle) := by
  unfold targetTurn
  split
  · exact AddCircle.coe_add_period (1 : ℝ) u
  · simp only [add_zero]

def segmentFamily {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (j : Fin 13) :
    NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I ⟶ SelfCutThomCocycle.parameters n :=
  MovingTimeTriangleGeometry.segment (NativeNorthCutClocks.breakClock P k j.castSucc)
    (NativeNorthCutClocks.breakClock P k j.succ) ≫ cutMap P v₀ k

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem endpoint_segment {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (j : Fin 13)
    (z : NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I) :
    H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k j z) =
      SobolevCircleRepresentative.sphereCircleMap (NativeH1TripleMeridian.native P v₀ z.1.2)
        (((clock k 0 z.1.1 : ℝ) : SobolevCircleRepresentative.Circle) +
          (((1 - (z.2.down : ℝ)) * (NativeNorthCutClocks.breakTime k j.castSucc z.1.1 : ℝ) +
            (z.2.down : ℝ) * (NativeNorthCutClocks.breakTime k j.succ z.1.1 : ℝ) : ℝ) : SobolevCircleRepresentative.Circle)) := by
  exact NativeTripleSelfEvaluation.endpoint_shift (NativeH1TripleMeridian.native P v₀ z.1.2)
    (clock k 0 z.1.1) (segmentFamily P v₀ k j z).1

theorem nonnorth_endpoint {n : ℕ} (P : Sphere n) (v₀ : equator P) (k i q : Fin 3)
    (z : NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I) :
    H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k (nonnorthSegment i q) z) =
      piece P v₀ (NativeTripleSelfEvaluation.directions z.1.2 (targetLeg k i))
        (NorthRotationPrismLocalization.nonNorthQuarter q) z.2.down := by
  rw [endpoint_segment, ← AddCircle.coe_add, target_clock, turn_period, NativeTripleSelfEvaluation.circle_quarter]

theorem nonnorth_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k i q : Fin 3)
    (z : NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I) :
    H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k (nonnorthSegment i q) z) ∈
      NorthMeridianEvaluationPoint.excluded P v₀ := by
  rw [nonnorth_endpoint]
  exact NorthRotationPrismLocalization.piece_excluded P v₀ _ q z.2.down

end
end Finsler.NativeMovingNonnorthGeometry
