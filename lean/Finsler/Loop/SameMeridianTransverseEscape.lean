module

public import Finsler.Loop.MeridianTransverseField
public import Finsler.Loop.OrthogonalSphereEscape
public import Finsler.Loop.NativeSameLegClockGeometry

/-! The real same-leg endpoint maps admit the orthogonal escape on
the ACTUAL local equator hemisphere. The old supported cap is zero
outside this patch by its original start-point carrier. This does not
yet discard the diagonal seam in the eventual full cap comparison. -/
@[expose] public section
namespace Finsler.SameMeridianTransverseEscape
open CategoryTheory SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.BorelEvaluation
open Finsler.RationalSphereArc Finsler.RationalSphereArcCoordinates Finsler.MeridianTripleQuarterClocks
open Finsler.NativeMovingNonnorthGeometry Finsler.NativeSameLegClockGeometry
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem north_perp {n : ℕ} (P : Sphere n) (v : equator P) (w : Sphere n)
    (hP : ⟪(P : Ambient n), (w : Ambient n)⟫ = 0)
    (hv : ⟪(v.val : Ambient n), (w : Ambient n)⟫ = 0) (s : ClosedInterval) :
    ⟪(point (outgoing P v) s : Ambient n), (w : Ambient n)⟫ = 0 := by
  rw [coordinates, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  change alpha s * ⟪(P : Ambient n), (w : Ambient n)⟫ + beta s * ⟪(v.val : Ambient n), (w : Ambient n)⟫ = 0
  rw [hP, hv, mul_zero, mul_zero, add_zero]

theorem first_near_direction {n : ℕ} (P : Sphere n) (v₀ v : equator P) (s : ClosedInterval)
    (h : ‖(point (outgoing P v) s : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 3 / 5) :
    v ∈ MeridianTransverseField.hemisphere P (NorthMeridianEvaluationPoint.opposite v₀) := by
  have hvP : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
  have hn : ⟪(v₀.val : Ambient n), (point (outgoing P v) s : Ambient n)⟫ < 0 := by
    by_contra hn
    have he := NorthMeridianEvaluationPoint.distance_fixed_side P v₀ (point (outgoing P v) s) (le_of_not_gt hn)
    linarith
  rw [coordinates, inner_add_right, real_inner_smul_right, real_inner_smul_right] at hn
  change alpha s * ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ + beta s * ⟪(v₀.val : Ambient n), (v.val : Ambient n)⟫ < 0 at hn
  rw [hvP, mul_zero, zero_add] at hn
  have hneg : ⟪(v₀.val : Ambient n), (v.val : Ambient n)⟫ < 0 := by
    nlinarith [beta_nonneg s]
  change 0 < ⟪(v.val : Ambient n), -(v₀.val : Ambient n)⟫
  rw [inner_neg_right, real_inner_comm]
  linarith

abbrev domain {n : ℕ} (P : Sphere n) := NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I

def localSet {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : Set (domain P) :=
  {z | NativeTripleSelfEvaluation.directions z.1.2 k ∈
    MeridianTransverseField.hemisphere P (NorthMeridianEvaluationPoint.opposite v₀)}
abbrev localSpace {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) := TopCat.of (localSet P v₀ k)

def direction {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    localSpace P v₀ k ⟶ MeridianTransverseField.space P (NorthMeridianEvaluationPoint.opposite v₀) :=
  TopCat.ofHom ⟨fun z => ⟨NativeTripleSelfEvaluation.directions z.val.1.2 k, z.property⟩, by
    apply Continuous.subtype_mk
    change Continuous (fun z : {z : (ClosedInterval × NativeH1TripleMeridian.parameters P) × ULift ClosedInterval // z ∈ localSet P v₀ k} =>
      NativeTripleSelfEvaluation.directions z.val.1.2 k)
    fin_cases k <;> dsimp [NativeTripleSelfEvaluation.directions] <;> fun_prop⟩

def normal {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) : localSpace P v₀ k ⟶ sphere n :=
  direction P v₀ k ≫ MeridianTransverseField.map hn P (NorthMeridianEvaluationPoint.opposite v₀)

def first {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : localSpace P v₀ k ⟶ sphere n :=
  SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 0 ≫
    TopCat.ofHom ⟨fun z => H1FiberBase.point z.2, H1FiberBase.continuous_point.comp continuous_snd⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem first_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : localSpace P v₀ k) :
    first P v₀ k z = piece P v₀ (NativeTripleSelfEvaluation.directions z.val.1.2 k) 0 z.val.1.1 := by
  change H1FiberBase.point (SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀ z.val.1.2)
    (clock k 0 z.val.1.1)) = _
  rw [NativeTripleSelfEvaluation.point_shift, NativeTripleSelfEvaluation.circle_quarter]

def shortEnd {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : localSpace P v₀ k ⟶ sphere n :=
  SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 0 ≫
    TopCat.ofHom ⟨H1SelfCutNeighborhood.endpoint, H1SelfCutNeighborhood.continuous_endpoint⟩

def longEnd {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : localSpace P v₀ k ⟶ sphere n :=
  SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 12 ≫
    TopCat.ofHom ⟨H1SelfCutNeighborhood.endpoint, H1SelfCutNeighborhood.continuous_endpoint⟩

theorem first_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : localSpace P v₀ k) :
    ⟪(first P v₀ k z : Ambient n), (normal hn P v₀ k z : Ambient n)⟫ = 0 := by
  rw [first_value]
  exact north_perp P _ _ (MeridianTransverseField.field_pole_perp hn P _ (direction P v₀ k z))
    (MeridianTransverseField.field_perp hn P _ (direction P v₀ k z)) z.val.1.1

theorem short_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : localSpace P v₀ k) :
    ⟪(shortEnd P v₀ k z : Ambient n), (normal hn P v₀ k z : Ambient n)⟫ = 0 := by
  change ⟪(H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 0 z.val) : Ambient n), _⟫ = 0
  rw [short_endpoint]
  exact north_perp P _ _ (MeridianTransverseField.field_pole_perp hn P _ (direction P v₀ k z))
    (MeridianTransverseField.field_perp hn P _ (direction P v₀ k z)) _

theorem long_perp {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : localSpace P v₀ k) :
    ⟪(longEnd P v₀ k z : Ambient n), (normal hn P v₀ k z : Ambient n)⟫ = 0 := by
  change ⟪(H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k 12 z.val) : Ambient n), _⟫ = 0
  rw [long_endpoint]
  exact north_perp P _ _ (MeridianTransverseField.field_pole_perp hn P _ (direction P v₀ k z))
    (MeridianTransverseField.field_perp hn P _ (direction P v₀ k z)) _

end
end Finsler.SameMeridianTransverseEscape
