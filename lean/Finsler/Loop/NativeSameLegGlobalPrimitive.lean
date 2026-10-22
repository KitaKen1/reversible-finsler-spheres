module

public import Finsler.Loop.NativeSameLegGlobalCochain
public import Finsler.Loop.PatchCochainPrimitive
public import Finsler.Loop.CochainCarrierPullbackZero

/-! A genuine GLOBAL primitive for the ORIGINAL full same-leg
cochain, obtained from the same local normal escape, actual zero
extension, and actual subdivision prism. Literal zeros on each real
time boundary are preserved separately; no arbitrary face-union zero
is assumed. The original tested/evaluation output is retained. -/
@[expose] public section
namespace Finsler.NativeSameLegGlobalPrimitive
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def exterior {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) : Set (domain P) :=
  NativeSameLegPatchGeometry.outside P v₀ k isLong (1 / 4)

variable (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
  {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (hr : r ≤ 1) (hη : 0 < η)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)

theorem overlap_outside_zero (hηr : η + r ≤ 1 / 4) :
    cochainPullback (PatchCochainPrimitive.overlapMap (domain P) (localSet P v₀ k) (exterior P v₀ k isLong))
      (m + (p + (m + 1)))
      (NativeSameLegLocalPrimitiveFaces.primitive m hm p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hρ1 hr hη T) = 0 :=
  CochainCarrierPullbackZero.family_zero
    (NativeSameLegCapSupport.outside P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) (1 / 4)) _ _
    (NativeSameLegLocalPrimitiveFaces.outside_zero m hm p P v₀ k isLong _ hρ hρr hρ1 hr hη T hηr) _
    (fun z => Or.inl z.val.property.le)

def primitive : singularCochainGroup (ZMod 2) (domain P) (m + (p + (m + 1))) :=
  PatchCochainPrimitive.primitive (domain P) (localSet P v₀ k) (exterior P v₀ k isLong) (m + (p + (m + 1)))
    (NativeSameLegGlobalCochain.cochain m p P v₀ k isLong hρ hρr hr hη T)
    (NativeSameLegLocalPrimitiveFaces.primitive m hm p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hρ1 hr hη T)

theorem boundary (hηr : η + r ≤ 1 / 4) (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (domain P) (m + (p + (m + 1)))
      (primitive m hm p P v₀ k isLong hρ hρr hρ1 hr hη T) =
      NativeSameLegGlobalCochain.cochain m p P v₀ k isLong hρ hρr hr hη T :=
  PatchCochainPrimitive.primitive_boundary (domain P) (localSet P v₀ k) (exterior P v₀ k isLong) _ _ _
    (NativeSameLegPatchGeometry.local_open P v₀ k) (NativeSameLegPatchGeometry.outside_open P v₀ k isLong _)
    (NativeSameLegPatchGeometry.cover P v₀ k isLong (by norm_num))
    (NativeSameLegGlobalCochain.closed m p P v₀ k isLong hρ hρr hr hη T hT)
    ((NativeSameLegLocalPrimitiveFaces.boundary m hm p P v₀ k isLong _ hρ hρr hρ1 hr hη T hT).trans
      (NativeSameLegGlobalCochain.local_restriction m p P v₀ k isLong hρ hρr hr hη T).symm)
    (NativeSameLegGlobalCochain.outside_zero m p P v₀ k isLong hρ hρr hr hη T hηr)
    (overlap_outside_zero m hm p P v₀ k isLong hρ hρr hρ1 hr hη T hηr)

theorem rotation_zero (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap (domain P) (NativeSameLegPatchGeometry.rotationEnds P))
      (m + (p + (m + 1))) (primitive m hm p P v₀ k isLong hρ hρr hρ1 hr hη T) = 0 :=
  PatchCochainPrimitive.primitive_carrier_zero (domain P) (localSet P v₀ k) (exterior P v₀ k isLong) _ _ _ _
    (NativeSameLegGlobalCochain.rotation_zero m p P v₀ k isLong hρ hρr hr hη T hη2)
    (CochainCarrierPullbackZero.family_zero (NativeSameLegBoundaryGeometry.rotationEnds P v₀ k) _ _
      (NativeSameLegLocalPrimitiveFaces.rotation_zero m hm p P v₀ k isLong hρ hρr hρ1 hr hη T hη2) _
      (fun z => z.val.property))

theorem other_end_zero (hηr : η + r ≤ 3 / 5) :
    cochainPullback (SupportedCap.subspaceMap (domain P) (NativeSameLegPatchGeometry.otherCutEnd P isLong))
      (m + (p + (m + 1))) (primitive m hm p P v₀ k isLong hρ hρr hρ1 hr hη T) = 0 :=
  PatchCochainPrimitive.primitive_carrier_zero (domain P) (localSet P v₀ k) (exterior P v₀ k isLong) _ _ _ _
    (NativeSameLegGlobalCochain.other_end_zero m p P v₀ k isLong hρ hρr hr hη T hηr)
    (CochainCarrierPullbackZero.family_zero (NativeSameLegBoundaryGeometry.otherCutEnd P v₀ k isLong) _ _
      (NativeSameLegLocalPrimitiveFaces.other_end_zero m hm p P v₀ k isLong hρ hρr hρ1 hr hη T hηr) _
      (fun z => z.val.property))

theorem seam_zero :
    cochainPullback (SupportedCap.subspaceMap (domain P) (NativeSameLegPatchGeometry.seam P isLong))
      (m + (p + (m + 1))) (primitive m hm p P v₀ k isLong hρ hρr hρ1 hr hη T) = 0 :=
  PatchCochainPrimitive.primitive_carrier_zero (domain P) (localSet P v₀ k) (exterior P v₀ k isLong) _ _ _ _
    (NativeSameLegGlobalCochain.seam_zero m p P v₀ k isLong hρ hρr hr hη T)
    (CochainCarrierPullbackZero.family_zero (NativeSameLegThomPrimitive.seam P v₀ k isLong) _ _
      (NativeSameLegLocalPrimitiveFaces.seam_zero m hm p P v₀ k isLong hρ hρr hρ1 hr hη T) _
      (fun z => z.val.property))

end
end Finsler.NativeSameLegGlobalPrimitive
