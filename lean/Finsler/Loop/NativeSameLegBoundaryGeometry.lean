module

public import Finsler.Loop.NativeSameLegCapSupport

/-! The actual rotation-end and opposite cut-end carriers are excluded;
the other cut end is the true diagonal seam. These are separate REAL
boundary components, without replacing their singular-chain union. -/
@[expose] public section
namespace Finsler.NativeSameLegBoundaryGeometry
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

def rotationEnds {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : Set (localSpace P v₀ k) :=
  {z | z.val.1.1 = 0 ∨ z.val.1.1 = 1}

def otherCutEnd {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) : Set (localSpace P v₀ k) :=
  {z | z.val.2.down = if isLong then 0 else 1}

theorem rotation_start_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    (z : localSpace P v₀ k) (hz : z ∈ rotationEnds P v₀ k) :
    H1FiberBase.point (family P v₀ k isLong z).2 ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  change H1FiberBase.point (segmentFamily P v₀ k (cutIndex isLong) z.val).2 ∈ _
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
    exact Or.inr (NativeTripleSelfEvaluation.directions z.val.1.2 k).property.le

theorem other_endpoint_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    (z : localSpace P v₀ k) (hz : z ∈ otherCutEnd P v₀ k isLong) :
    H1SelfCutNeighborhood.endpoint (family P v₀ k isLong z) ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  cases isLong
  · change H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 0 z.val) ∈ _
    rw [NativeSameLegClockGeometry.short_endpoint]
    have ht : NativeSameLegClockGeometry.later z.val.1.1 z.val.2.down = 1 := by
      apply Subtype.ext
      change z.val.2.down = (1 : ClosedInterval) at hz
      rw [hz]
      change (z.val.1.1 : ℝ) + (1 - (z.val.1.1 : ℝ)) * 1 = 1
      ring
    rw [ht]
    change point (outgoing P _) 1 ∈ _
    rw [point_one]
    exact Or.inr (NativeTripleSelfEvaluation.directions z.val.1.2 k).property.le
  · change H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 12 z.val) ∈ _
    rw [NativeSameLegClockGeometry.long_endpoint]
    have ht : NativeSameLegClockGeometry.earlier z.val.1.1 z.val.2.down = 0 := by
      apply Subtype.ext
      change z.val.2.down = (0 : ClosedInterval) at hz
      rw [hz]
      change (z.val.1.1 : ℝ) * 0 = 0
      ring
    rw [ht]
    change point (outgoing P _) 0 ∈ _
    rw [point_zero]
    apply Or.inl
    have he : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
    exact he.ge

theorem seam_diagonal {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    (z : localSpace P v₀ k) (hz : z ∈ seam P v₀ k isLong) :
    H1FiberBase.point (family P v₀ k isLong z).2 = H1SelfCutNeighborhood.endpoint (family P v₀ k isLong z) := by
  let V := NorthMeridianEvaluationPoint.opposite v₀
  have hm := input_seam P v₀ k isLong z hz
  have he := ConcreteCategory.congr_hom (input_pair P v₀ k isLong) z
  change (firstPoint P V (input P v₀ k isLong z), secondPoint P V (input P v₀ k isLong z)) =
    (H1FiberBase.point (family P v₀ k isLong z).2, H1SelfCutNeighborhood.endpoint (family P v₀ k isLong z)) at he
  have hpts : firstPoint P V (input P v₀ k isLong z) = secondPoint P V (input P v₀ k isLong z) :=
    congrArg (point (outgoing P (input P v₀ k isLong z).2.val)) hm
  have ha := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  change firstPoint P V (input P v₀ k isLong z) = H1FiberBase.point (family P v₀ k isLong z).2 at ha
  change secondPoint P V (input P v₀ k isLong z) = H1SelfCutNeighborhood.endpoint (family P v₀ k isLong z) at hb
  exact ha.symm.trans (hpts.trans hb)

end
end Finsler.NativeSameLegBoundaryGeometry
