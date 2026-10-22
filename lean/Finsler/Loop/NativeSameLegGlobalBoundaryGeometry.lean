module

public import Finsler.Loop.NativeSameLegPatchGeometry

/-! The actual rotation-end and opposite cut-end carriers are excluded;
the other cut end is the true diagonal seam. These are separate REAL
boundary components, without replacing their singular-chain union. -/
@[expose] public section
namespace Finsler.NativeSameLegGlobalBoundaryGeometry
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive Finsler.NativeMovingNonnorthGeometry
open Finsler.MeridianTripleQuarterClocks Finsler.RationalSphereArc Finsler.RationalSphereArcCoordinates
open Finsler.CommonMeridianThomPrimitive
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem rotation_start_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    (z : domain P) (hz : z ∈ NativeSameLegPatchGeometry.rotationEnds P) :
    H1FiberBase.point (segmentFamily P v₀ k (cutIndex isLong) z).2 ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  rw [NativeSameLegThomReduction.original_start]
  rcases hz with h | h
  · rw [h]
    change point (outgoing P _) 0 ∈ _
    rw [point_zero]
    apply Or.inl
    have he : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
    exact he.ge
  · rw [h]
    change point (outgoing P _) 1 ∈ _
    rw [point_one]
    exact Or.inr (NativeTripleSelfEvaluation.directions z.1.2 k).property.le

theorem other_endpoint_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    (z : domain P) (hz : z ∈ NativeSameLegPatchGeometry.otherCutEnd P isLong) :
    H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k (cutIndex isLong) z) ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  cases isLong
  · change H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 0 z) ∈ _
    rw [NativeSameLegClockGeometry.short_endpoint]
    have ht : NativeSameLegClockGeometry.later z.1.1 z.2.down = 1 := by
      apply Subtype.ext
      change z.2.down = (1 : ClosedInterval) at hz
      rw [hz]
      change (z.1.1 : ℝ) + (1 - (z.1.1 : ℝ)) * 1 = 1
      ring
    rw [ht]
    change point (outgoing P _) 1 ∈ _
    rw [point_one]
    exact Or.inr (NativeTripleSelfEvaluation.directions z.1.2 k).property.le
  · change H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 12 z) ∈ _
    rw [NativeSameLegClockGeometry.long_endpoint]
    have ht : NativeSameLegClockGeometry.earlier z.1.1 z.2.down = 0 := by
      apply Subtype.ext
      change z.2.down = (0 : ClosedInterval) at hz
      rw [hz]
      change (z.1.1 : ℝ) * 0 = 0
      ring
    rw [ht]
    change point (outgoing P _) 0 ∈ _
    rw [point_zero]
    apply Or.inl
    have he : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
    exact he.ge

theorem seam_diagonal {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    (z : domain P) (hz : z ∈ NativeSameLegPatchGeometry.seam P isLong) :
    H1FiberBase.point (segmentFamily P v₀ k (cutIndex isLong) z).2 =
      H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k (cutIndex isLong) z) := by
  rw [NativeSameLegThomReduction.original_start]
  cases isLong
  · change piece P v₀ (NativeTripleSelfEvaluation.directions z.1.2 k) 0 z.1.1 =
      H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 0 z)
    rw [NativeSameLegClockGeometry.short_endpoint]
    change z.2.down = (0 : ClosedInterval) at hz
    rw [hz, NativeSameLegClockGeometry.short_diagonal]
  · change piece P v₀ (NativeTripleSelfEvaluation.directions z.1.2 k) 0 z.1.1 =
      H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 12 z)
    rw [NativeSameLegClockGeometry.long_endpoint]
    change z.2.down = (1 : ClosedInterval) at hz
    rw [hz, NativeSameLegClockGeometry.long_diagonal]

end
end Finsler.NativeSameLegGlobalBoundaryGeometry
