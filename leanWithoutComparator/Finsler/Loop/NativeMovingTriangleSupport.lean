module

public import Finsler.Loop.MovingTimeTriangleChain
public import Finsler.Loop.NativeGlobalSquareFaceZero
public import Finsler.Loop.RelativePrismCochainBoundary

/-! The actual moving-clock triangle retains the ORIGINAL rotation
source. On its rotation-boundary carrier, the original localized
parameter cochain is literally zero. Its comparison cochain therefore
kills the boundary of the actual rotation prism, without treating that
prism as an absolute cycle or merging independent square face unions. -/
@[expose] public section
namespace Finsler.NativeMovingTriangleSupport
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def cutMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I ⟶ SelfCutThomCocycle.parameters n :=
  (DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.rotationDomain P)).h ≫
    NativeGlobalTimeSquare.intoCut P v₀ k

def sourceBoundary {n : ℕ} (P : Sphere n) : Set (NativeGlobalTimeSquare.rotationDomain P) :=
  DoubleRelativeTimeCylinder.boundary (NativeGlobalTimeSquare.source P)

def boundaryInclusion {n : ℕ} (P : Sphere n) :
    TopCat.of (sourceBoundary P) ⟶ NativeGlobalTimeSquare.rotationDomain P :=
  SupportedCap.subspaceMap (NativeGlobalTimeSquare.rotationDomain P) (sourceBoundary P)

def boundaryFamily {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    (a : Fin 3 → (NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I)) :
    TopCat.of (sourceBoundary P) ⊗ UniversalTimeTriangle.space ⟶ SelfCutThomCocycle.parameters n :=
  (boundaryInclusion P ▷ UniversalTimeTriangle.space) ≫
    (MovingTimeTriangleGeometry.triangleMap a ≫ cutMap P v₀ k)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem boundary_start_excluded (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    (a : Fin 3 → (NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I))
    (z : TopCat.of (sourceBoundary P) ⊗ UniversalTimeTriangle.space) :
    H1FiberBase.point (boundaryFamily P v₀ k a z).2 ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  have he : H1FiberBase.point (boundaryFamily P v₀ k a z).2 =
      H1FiberBase.point (NativeGlobalTimeSquare.northRotation P v₀ k z.1.val) := rfl
  rw [he]
  change H1FiberBase.point (NativeFixedReturnRotationZero.quarterFamily P v₀ k 0
    (z.1.val.1, z.1.val.2)) ∈ _
  rcases z.1.property with h | h
  · rw [h]
    exact NorthRotationPrismLocalization.north_start_excluded P v₀ k z.1.val.2
  · rw [h]
    exact NorthRotationPrismLocalization.north_finish_excluded P v₀ k z.1.val.2

theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h φ) =
      CochainDegreeTransport.pre X h (cochainPullback f j φ) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem boundary_parameter_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    (a : Fin 3 → (NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    cochainPullback (boundaryFamily P v₀ k a) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) = 0 := by
  have hz := NativeGlobalSquareFaceZero.parameter_start_family_zero m m P v₀ hρ hρr hr hη hη2
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (boundaryFamily P v₀ k a)
    (boundary_start_excluded m P v₀ k a)
  rw [GlobalCutTimePrismAlignment.parameterCochain, pullback_pre, hz, CochainDegreeTransport.pre, comp_zero]

theorem comparison_boundary_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    (a : Fin 3 → (NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    cochainPullback (boundaryInclusion P) (3 * m)
      (MovingTimeTriangleChain.comparison (cutMap P v₀ k) a (3 * m) ≫
        GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) = 0 :=
  UniversalTimeTriangleChain.source_carrier_zero (boundaryInclusion P)
    (MovingTimeTriangleGeometry.triangleMap a ≫ cutMap P v₀ k) (3 * m)
    (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)
    (boundary_parameter_zero m P v₀ k a hρ hρr hr hη hη2)

theorem source_boundary_term_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    (a : Fin 3 → (NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    (chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      ((DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.source P)).toSSet.chainComplexMap coeff).hom
        (3 * m) (3 * m + 1) ≫
      (chains (NativeGlobalTimeSquare.rotationDomain P)).d (3 * m + 1) (3 * m) ≫
      MovingTimeTriangleChain.comparison (cutMap P v₀ k) a (3 * m) ≫
      GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη = 0 := by
  exact RelativePrismCochainBoundary.ordinary_boundary_zero (sourceBoundary P)
    (DoubleRelativeTimeCylinder.homotopy (NativeGlobalTimeSquare.source P))
    (fun _ => Or.inl rfl) (fun _ => Or.inr rfl) (3 * m)
    (MovingTimeTriangleChain.comparison (cutMap P v₀ k) a (3 * m) ≫
      GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)
    (comparison_boundary_zero m P v₀ k a hρ hρr hr hη hη2)

end
end Finsler.NativeMovingTriangleSupport
