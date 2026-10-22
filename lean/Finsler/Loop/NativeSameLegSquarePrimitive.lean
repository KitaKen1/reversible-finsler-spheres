module

public import Finsler.Loop.NativeSameLegGlobalPrimitive
public import Finsler.Loop.DoublePrismCochainBoundary
public import Finsler.Loop.NativeMovingSquareChain

/-! Transport the SAME global primitive to the original double
prism coordinates and exact degree3m+1. Its boundary is the ORIGINAL
segment cochain in degree3m+2; the two cut endpoints and rotation
boundary cylinder vanish separately. -/
@[expose] public section
namespace Finsler.NativeSameLegSquarePrimitive
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.NativeMovingOrderedChartAlignment Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem pre_boundary (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (κ : singularCochainGroup (ZMod 2) X j) :
    cochainCoboundary (ZMod 2) X i (CochainDegreeTransport.pre X h κ) =
      CochainDegreeTransport.pre X (congrArg (· + 1) h) (cochainCoboundary (ZMod 2) X j κ) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
  {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)

def primitive : singularCochainGroup (ZMod 2) (NativeGlobalTimeSquare.squareDomain P) (3 * m + 1) :=
  CochainDegreeTransport.pre _ (by omega : 3 * m + 1 = m + (m + (m + 1)))
    (cochainPullback (assembledCoordinates P 0) (m + (m + (m + 1)))
      (NativeSameLegGlobalPrimitive.primitive m hm m P v₀ k isLong hρ hρr (le_trans hρr.le hr) hr hη
        (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))))

theorem boundary (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    cochainCoboundary (ZMod 2) (NativeGlobalTimeSquare.squareDomain P) (3 * m + 1)
      (primitive m hm P v₀ k isLong hρ hρr hr hη) =
      cochainPullback (assembledCoordinates P 0 ≫ NativeMovingNonnorthGeometry.segmentFamily P v₀ k (cutIndex isLong)) (3 * m + 2)
        (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) := by
  rw [primitive, pre_boundary]
  have he := SmallChainPrimitiveCorrection.pullback_boundary (assembledCoordinates P 0)
    (m + (m + (m + 1))) (m + (m + (m + 1)) + 1)
    (NativeSameLegGlobalPrimitive.primitive m hm m P v₀ k isLong hρ hρr (le_trans hρr.le hr) hr hη
      (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))
  change cochainCoboundary (ZMod 2) (NativeGlobalTimeSquare.squareDomain P) (m + (m + (m + 1)))
      (cochainPullback (assembledCoordinates P 0) (m + (m + (m + 1))) _) =
    cochainPullback (assembledCoordinates P 0) (m + (m + (m + 1)) + 1)
      (cochainCoboundary (ZMod 2) (domain P) (m + (m + (m + 1))) _) at he
  rw [he, NativeSameLegGlobalPrimitive.boundary m hm m P v₀ k isLong hρ hρr (le_trans hρr.le hr) hr hη _
    (by linarith) (classRepr_isCocycle _ m _)]
  unfold NativeSameLegGlobalCochain.cochain NativeSameLegLocalPrimitiveFaces.parameter GlobalCutTimePrismAlignment.parameterCochain
  rw [← pullback_comp]
  simp only [NativeMovingTriangleSupport.pullback_pre, GlobalCutTimePrismAlignment.pre_trans]

theorem zero_family {Y : TopCat.{0}} (f : Y ⟶ NativeGlobalTimeSquare.squareDomain P)
    (hf : cochainPullback (f ≫ assembledCoordinates P 0) (m + (m + (m + 1)))
      (NativeSameLegGlobalPrimitive.primitive m hm m P v₀ k isLong hρ hρr (le_trans hρr.le hr) hr hη
        (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))) = 0) :
    cochainPullback f (3 * m + 1) (primitive m hm P v₀ k isLong hρ hρr hr hη) = 0 := by
  rw [primitive, NativeMovingTriangleSupport.pullback_pre, ← pullback_comp, hf, CochainDegreeTransport.pre, comp_zero]

theorem at_zero_zero (hηr : η + r ≤ 3 / 5) :
    cochainPullback (DoubleRelativeTimeCylinder.atTime (NativeGlobalTimeSquare.rotationDomain P) 0) (3 * m + 1)
      (primitive m hm P v₀ k isLong hρ hρr hr hη) = 0 := by
  apply zero_family m hm P v₀ k isLong hρ hρr hr hη
  cases isLong
  · exact CochainCarrierPullbackZero.family_zero (NativeSameLegPatchGeometry.seam P false) _ _
      (NativeSameLegGlobalPrimitive.seam_zero m hm m P v₀ k false hρ hρr (le_trans hρr.le hr) hr hη _) _ (fun _ => rfl)
  · exact CochainCarrierPullbackZero.family_zero (NativeSameLegPatchGeometry.otherCutEnd P true) _ _
      (NativeSameLegGlobalPrimitive.other_end_zero m hm m P v₀ k true hρ hρr (le_trans hρr.le hr) hr hη _ hηr) _ (fun _ => rfl)

theorem at_one_zero (hηr : η + r ≤ 3 / 5) :
    cochainPullback (DoubleRelativeTimeCylinder.atTime (NativeGlobalTimeSquare.rotationDomain P) 1) (3 * m + 1)
      (primitive m hm P v₀ k isLong hρ hρr hr hη) = 0 := by
  apply zero_family m hm P v₀ k isLong hρ hρr hr hη
  cases isLong
  · exact CochainCarrierPullbackZero.family_zero (NativeSameLegPatchGeometry.otherCutEnd P false) _ _
      (NativeSameLegGlobalPrimitive.other_end_zero m hm m P v₀ k false hρ hρr (le_trans hρr.le hr) hr hη _ hηr) _ (fun _ => rfl)
  · exact CochainCarrierPullbackZero.family_zero (NativeSameLegPatchGeometry.seam P true) _ _
      (NativeSameLegGlobalPrimitive.seam_zero m hm m P v₀ k true hρ hρr (le_trans hρr.le hr) hr hη _) _ (fun _ => rfl)

theorem rotation_zero (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap _ (DoublePrismCochainBoundary.rotationFaces (NativeGlobalTimeSquare.source P))) (3 * m + 1)
      (primitive m hm P v₀ k isLong hρ hρr hr hη) = 0 :=
  zero_family m hm P v₀ k isLong hρ hρr hr hη _
    (CochainCarrierPullbackZero.family_zero (NativeSameLegPatchGeometry.rotationEnds P) _ _
      (NativeSameLegGlobalPrimitive.rotation_zero m hm m P v₀ k isLong hρ hρr (le_trans hρr.le hr) hr hη _ hη2) _
      (fun z => z.property))

end
end Finsler.NativeSameLegSquarePrimitive
