module

public import Finsler.Loop.NativeSameLegLocalPrimitiveFaces
public import Finsler.Loop.NativeSameLegGlobalBoundaryGeometry

/-! The ORIGINAL full localized cochain on the ENTIRE actual
same-leg source. Its separate rotation/cut face zeros and actual
open-exterior zero are proved directly, before any patch gluing. -/
@[expose] public section
namespace Finsler.NativeSameLegGlobalCochain
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.NativeMovingNonnorthGeometry Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
  {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)

def cochain : singularCochainGroup (ZMod 2) (domain P) (m + (p + (m + 1)) + 1) :=
  cochainPullback (segmentFamily P v₀ k (cutIndex isLong)) (m + (p + (m + 1)) + 1)
    (NativeSameLegLocalPrimitiveFaces.parameter m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T)

theorem closed (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (domain P) (m + (p + (m + 1)) + 1) (cochain m p P v₀ k isLong hρ hρr hr hη T) = 0 :=
  pullback_closed _ _ _ (CochainDegreeTransport.closed _ _ _
    (LocalizedParameterCutCochain.closed m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T hT))

theorem local_restriction : cochainPullback (SupportedCap.subspaceMap (domain P) (localSet P v₀ k))
    (m + (p + (m + 1)) + 1) (cochain m p P v₀ k isLong hρ hρr hr hη T) =
    cochainPullback (family P v₀ k isLong) (m + (p + (m + 1)) + 1)
      (NativeSameLegLocalPrimitiveFaces.parameter m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) := by
  rw [cochain, ← pullback_comp]
  rfl

theorem family_zero {Y : TopCat.{0}} (f : Y ⟶ domain P)
    (hf : cochainPullback (f ≫ segmentFamily P v₀ k (cutIndex isLong)) ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) = 0) :
    cochainPullback f (m + (p + (m + 1)) + 1) (cochain m p P v₀ k isLong hρ hρr hr hη T) = 0 := by
  rw [cochain, ← pullback_comp, NativeSameLegLocalPrimitiveFaces.parameter,
    NativeMovingTriangleSupport.pullback_pre, hf, CochainDegreeTransport.pre, comp_zero]

theorem outside_zero {D : ℝ} (hηr : η + r ≤ D) :
    cochainPullback (SupportedCap.subspaceMap (domain P) (NativeSameLegPatchGeometry.outside P v₀ k isLong D))
      (m + (p + (m + 1)) + 1) (cochain m p P v₀ k isLong hρ hρr hr hη T) = 0 :=
  family_zero m p P v₀ k isLong hρ hρr hr hη T _
    (LocalizedParameterCutCochain.family_zero m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη hηr T _
      (fun z => Or.inl z.property.le))

theorem rotation_zero (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap (domain P) (NativeSameLegPatchGeometry.rotationEnds P))
      (m + (p + (m + 1)) + 1) (cochain m p P v₀ k isLong hρ hρr hr hη T) = 0 :=
  family_zero m p P v₀ k isLong hρ hρr hr hη T _
    (NativeGlobalSquareFaceZero.parameter_start_family_zero m p P v₀ hρ hρr hr hη hη2 T _
      (fun z => NativeSameLegGlobalBoundaryGeometry.rotation_start_excluded P v₀ k isLong z.val z.property))

theorem other_end_zero (hηr : η + r ≤ 3 / 5) :
    cochainPullback (SupportedCap.subspaceMap (domain P) (NativeSameLegPatchGeometry.otherCutEnd P isLong))
      (m + (p + (m + 1)) + 1) (cochain m p P v₀ k isLong hρ hρr hr hη T) = 0 :=
  family_zero m p P v₀ k isLong hρ hρr hr hη T _
    (LocalizedParameterCutCochain.family_zero m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη hηr T _
      (fun z => Or.inr (NorthMeridianEvaluationPoint.excluded_distance P v₀
        ⟨H1SelfCutNeighborhood.endpoint (segmentFamily P v₀ k (cutIndex isLong) z.val),
          NativeSameLegGlobalBoundaryGeometry.other_endpoint_excluded P v₀ k isLong z.val z.property⟩)))

theorem seam_zero :
    cochainPullback (SupportedCap.subspaceMap (domain P) (NativeSameLegPatchGeometry.seam P isLong))
      (m + (p + (m + 1)) + 1) (cochain m p P v₀ k isLong hρ hρr hr hη T) = 0 :=
  family_zero m p P v₀ k isLong hρ hρr hr hη T _
    (DiagonalParameterCutZero.family_zero m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T _
      (fun z => NativeSameLegGlobalBoundaryGeometry.seam_diagonal P v₀ k isLong z.val z.property))

end
end Finsler.NativeSameLegGlobalCochain
