module

public import Finsler.Loop.NativeSameLegSupportedPrimitive
public import Finsler.Loop.NativeMovingTriangleSupport

/-! The explicit primitive of the ORIGINAL localized complete cap
has literal zero on each actual time face and start/end-far carrier.
All zeros survive the actual subdivision-prism correction. -/
@[expose] public section
namespace Finsler.NativeSameLegLocalPrimitiveFaces
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.NativeSameLegCapSupport Finsler.NativeSameLegBoundaryGeometry
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
  (Q : Sphere (m + 1)) {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (hr : r ≤ 1) (hη : 0 < η)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)

def parameter : singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) (m + (p + (m + 1)) + 1) :=
  CochainDegreeTransport.pre _ (by omega : m + (p + (m + 1)) + 1 = (m + 1) + (p + (m + 1)))
    (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T)

theorem original_parameter : NativeSameLegSupportedPrimitive.original m P v₀ k isLong hρ hρr (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p Q hr hη T) =
      cochainPullback (family P v₀ k isLong) (m + (p + (m + 1)) + 1) (parameter m p Q hρ hρr hr hη T) := by
  rw [NativeSameLegSupportedPrimitive.original_eq, NativeSameLegLocalizedClass.original_eq, parameter,
    NativeMovingTriangleSupport.pullback_pre]

def primitive : singularCochainGroup (ZMod 2) (localSpace P v₀ k) (m + (p + (m + 1))) :=
  NativeSameLegSupportedPrimitive.primitive m P v₀ k isLong hρ hρr (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p Q hr hη T) hm hρ1

theorem boundary (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (localSpace P v₀ k) (m + (p + (m + 1)))
      (primitive m hm p P v₀ k isLong Q hρ hρr hρ1 hr hη T) =
      cochainPullback (family P v₀ k isLong) (m + (p + (m + 1)) + 1) (parameter m p Q hρ hρr hr hη T) :=
  (NativeSameLegSupportedPrimitive.primitive_boundary m P v₀ k isLong hρ hρr (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p Q hr hη T) (NativeSameLegLocalizedClass.output_closed m p Q hr hη T hT) hm hρ1).trans
      (original_parameter m p P v₀ k isLong Q hρ hρr hr hη T)

theorem original_carrier_zero (C : Set (localSpace P v₀ k))
    (hC : cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) C ≫ family P v₀ k isLong)
      ((m + 1) + (p + (m + 1))) (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T) = 0) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) C) (m + (p + (m + 1)) + 1)
      (NativeSameLegSupportedPrimitive.original m P v₀ k isLong hρ hρr (p + (m + 1))
        (NativeSameLegLocalizedClass.output m p Q hr hη T)) = 0 := by
  rw [original_parameter, ← pullback_comp, parameter, NativeMovingTriangleSupport.pullback_pre, hC,
    CochainDegreeTransport.pre, comp_zero]

theorem outside_zero {D : ℝ} (hηr : η + r ≤ D) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (outside P v₀ k isLong Q D)) (m + (p + (m + 1)))
      (primitive m hm p P v₀ k isLong Q hρ hρr hρ1 hr hη T) = 0 :=
  NativeSameLegSupportedPrimitive.primitive_carrier_zero m P v₀ k isLong hρ hρr (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p Q hr hη T) hm hρ1 _
    (original_carrier_zero m p P v₀ k isLong Q hρ hρr hr hη T _
      (NativeSameLegOriginalBoundary.outside_zero m p P v₀ k isLong hρ hρr hr hη T Q hηr))
    (NativeSameLegCapSupport.correction_outside_zero m hm p P v₀ k isLong Q hρ hρr hρ1 hr hη hηr T)

theorem rotation_zero (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (rotationEnds P v₀ k)) (m + (p + (m + 1)))
      (primitive m hm p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hρ1 hr hη T) = 0 :=
  NativeSameLegSupportedPrimitive.primitive_carrier_zero m P v₀ k isLong hρ hρr (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p (NorthMeridianEvaluationPoint.target P v₀) hr hη T) hm hρ1 _
    (original_carrier_zero m p P v₀ k isLong _ hρ hρr hr hη T _
      (NativeSameLegOriginalBoundary.rotation_zero m p P v₀ k isLong hρ hρr hr hη T hη2))
    (NativeSameLegBoundarySupport.correction_rotation_zero m hm p P v₀ k isLong hρ hρr hρ1 hr hη T hη2)

theorem other_end_zero (hηr : η + r ≤ 3 / 5) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (otherCutEnd P v₀ k isLong)) (m + (p + (m + 1)))
      (primitive m hm p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hρ1 hr hη T) = 0 :=
  NativeSameLegSupportedPrimitive.primitive_carrier_zero m P v₀ k isLong hρ hρr (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p (NorthMeridianEvaluationPoint.target P v₀) hr hη T) hm hρ1 _
    (original_carrier_zero m p P v₀ k isLong _ hρ hρr hr hη T _
      (NativeSameLegOriginalBoundary.other_end_zero m p P v₀ k isLong hρ hρr hr hη T hηr))
    (NativeSameLegBoundarySupport.correction_other_end_zero m hm p P v₀ k isLong hρ hρr hρ1 hr hη T hηr)

theorem seam_zero :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (seam P v₀ k isLong)) (m + (p + (m + 1)))
      (primitive m hm p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hρ1 hr hη T) = 0 :=
  NativeSameLegSupportedPrimitive.primitive_carrier_zero m P v₀ k isLong hρ hρr (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p (NorthMeridianEvaluationPoint.target P v₀) hr hη T) hm hρ1 _
    (original_carrier_zero m p P v₀ k isLong _ hρ hρr hr hη T _
      (NativeSameLegOriginalBoundary.seam_zero m p P v₀ k isLong hρ hρr hr hη T))
    (NativeSameLegBoundarySupport.correction_seam_zero m hm p P v₀ k isLong hρ hρr hρ1 hr hη T)

end
end Finsler.NativeSameLegLocalPrimitiveFaces
