module

public import Finsler.Loop.NativeSameLegBoundarySupport
public import Finsler.Loop.DiagonalParameterCutZero

/-! Literal separate boundary and support zeros for the ORIGINAL
complete same-leg parameter cochain on the actual local patch. -/
@[expose] public section
namespace Finsler.NativeSameLegOriginalBoundary
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.NativeSameLegCapSupport Finsler.NativeSameLegBoundaryGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
  {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)

theorem rotation_zero (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (rotationEnds P v₀ k) ≫ family P v₀ k isLong)
      ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) = 0 :=
  NativeGlobalSquareFaceZero.parameter_start_family_zero m p P v₀ hρ hρr hr hη hη2 T _
    (fun z => rotation_start_excluded P v₀ k isLong z.val z.property)

theorem other_end_zero (hηr : η + r ≤ 3 / 5) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (otherCutEnd P v₀ k isLong) ≫ family P v₀ k isLong)
      ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) = 0 :=
  LocalizedParameterCutCochain.family_zero m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη hηr T _
    (fun z => Or.inr (NorthMeridianEvaluationPoint.excluded_distance P v₀
      ⟨H1SelfCutNeighborhood.endpoint (family P v₀ k isLong z.val), other_endpoint_excluded P v₀ k isLong z.val z.property⟩))

theorem seam_zero :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (seam P v₀ k isLong) ≫ family P v₀ k isLong)
      ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) = 0 :=
  DiagonalParameterCutZero.family_zero m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T _
    (fun z => seam_diagonal P v₀ k isLong z.val z.property)

theorem outside_zero (Q : Sphere (m + 1)) {D : ℝ} (hηr : η + r ≤ D) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (outside P v₀ k isLong Q D) ≫ family P v₀ k isLong)
      ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T) = 0 :=
  LocalizedParameterCutCochain.family_zero m p Q hρ hρr hr hη hηr T _ (fun z => z.property)

end
end Finsler.NativeSameLegOriginalBoundary
