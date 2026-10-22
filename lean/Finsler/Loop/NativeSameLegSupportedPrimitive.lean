module

public import Finsler.Loop.NativeSameLegOriginalBoundary
public import Finsler.Loop.SmallChainPrimitiveCorrection
public import Finsler.Loop.SupportedCapSmallDegree

/-! An explicit primitive for the ORIGINAL ambient complete cap on
the actual local patch. The real source-small cap comparison is
corrected by the actual subdivision prism, preserving each separately
specified carrier zero. This is a cochain boundary, beyond class zero. -/
@[expose] public section
namespace Finsler.NativeSameLegSupportedPrimitive
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
  {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q)
  (hψ : cochainCoboundary (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q ψ = 0)

def original : singularCochainGroup (ZMod 2) (localSpace P v₀ k) (m + q + 1) :=
  cochainPullback (family P v₀ k isLong) (m + q + 1)
    (SupportedCap.cut (SelfCutThomCocycle.parameters (m + 1))
      (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
      (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
      (SupportedSelfCut.cover (m + 1) hρr) (m + 1) q (m + q + 1) (by omega)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
      (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) ≫ ψ)

theorem original_eq : original m P v₀ k isLong hρ hρr q ψ =
    CochainDegreeTransport.pre (localSpace P v₀ k) (by omega : m + q + 1 = (m + 1) + q)
      (NativeSameLegOriginalCapClass.original m P v₀ k isLong hρ hρr q ψ) :=
  (SupportedCapSmallDegree.pullback_pre (family P v₀ k isLong)
    (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.cover (m + 1) hρr) (m + 1) q (m + q + 1) (by omega)
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) ψ).symm

include hψ in
theorem original_closed : cochainCoboundary (ZMod 2) (localSpace P v₀ k) (m + q + 1)
    (original m P v₀ k isLong hρ hρr q ψ) = 0 := by
  rw [original_eq]
  exact CochainDegreeTransport.closed _ _ _ (NativeSameLegOriginalCapClass.original_closed m P v₀ k isLong hρ hρr q ψ hψ)

variable (hm : 1 ≤ m) (hρ1 : ρ ≤ 1)

def proposed : singularCochainGroup (ZMod 2) (localSpace P v₀ k) (m + q) :=
  NativeSameLegLocalCap.correction m hm P v₀ k isLong hρ hρr hρ1 q
    (cochainPullback (NativeSameLegOriginalCapClass.nearMap P v₀ k isLong r) q ψ)

def sourceCover (ρ r : ℝ) : Bool → Set (localSpace P v₀ k) :=
  SupportedCap.cover (localSpace P v₀ k) (NativeSameLegLocalCap.exterior P v₀ k isLong ρ) (NativeSameLegLocalCap.near P v₀ k isLong r)

include hψ in
theorem small_boundary :
    (SmallChainCarrier.inclusion (localSpace P v₀ k) (sourceCover m P v₀ k isLong ρ r)).f (m + q + 1) ≫
      original m P v₀ k isLong hρ hρr q ψ =
    (SmallChainCarrier.inclusion (localSpace P v₀ k) (sourceCover m P v₀ k isLong ρ r)).f (m + q + 1) ≫
      cochainCoboundary (ZMod 2) (localSpace P v₀ k) (m + q) (proposed m P v₀ k isLong hρ hρr q ψ hm hρ1) := by
  have he : (SmallChainCarrier.inclusion (localSpace P v₀ k) (sourceCover m P v₀ k isLong ρ r)).f (m + q + 1) ≫
      original m P v₀ k isLong hρ hρr q ψ =
    (SmallChainCarrier.inclusion (localSpace P v₀ k) (sourceCover m P v₀ k isLong ρ r)).f (m + q + 1) ≫
      NativeSameLegLocalCap.cochain m P v₀ k isLong hρ hρr q
        (cochainPullback (NativeSameLegOriginalCapClass.nearMap P v₀ k isLong r) q ψ) :=
    SupportedCapSmallDegree.small_equality (family P v₀ k isLong)
      (NativeSameLegLocalCap.exterior P v₀ k isLong ρ) (NativeSameLegLocalCap.near P v₀ k isLong r)
      (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
      (NativeSameLegLocalCap.exterior_open P v₀ k isLong ρ) (NativeSameLegLocalCap.near_open P v₀ k isLong r)
      (NativeSameLegLocalCap.cover P v₀ k isLong hρr)
      (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
      (SupportedSelfCut.cover (m + 1) hρr) (fun _ h => h) (fun _ h => h)
      (m + 1) q (m + q + 1) (by omega) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
      (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) ψ
  exact he.trans (congrArg (fun a =>
    (SmallChainCarrier.inclusion (localSpace P v₀ k) (sourceCover m P v₀ k isLong ρ r)).f (m + q + 1) ≫ a)
    (NativeSameLegLocalCap.correction_boundary m hm P v₀ k isLong hρ hρr hρ1 q _
      (pullback_closed _ q ψ hψ)).symm)

def primitive : singularCochainGroup (ZMod 2) (localSpace P v₀ k) (m + q) :=
  SmallChainPrimitiveCorrection.primitive (sourceCover m P v₀ k isLong ρ r) (m + q)
    (original m P v₀ k isLong hρ hρr q ψ) (proposed m P v₀ k isLong hρ hρr q ψ hm hρ1)

include hψ in
theorem primitive_boundary :
    cochainCoboundary (ZMod 2) (localSpace P v₀ k) (m + q) (primitive m P v₀ k isLong hρ hρr q ψ hm hρ1) =
      original m P v₀ k isLong hρ hρr q ψ :=
  SmallChainPrimitiveCorrection.primitive_boundary (sourceCover m P v₀ k isLong ρ r) (m + q) _ _
    (SupportedCap.cover_open _ _ _ (NativeSameLegLocalCap.exterior_open P v₀ k isLong ρ) (NativeSameLegLocalCap.near_open P v₀ k isLong r))
    (SupportedCap.cover_univ _ _ _ (NativeSameLegLocalCap.cover P v₀ k isLong hρr))
    (original_closed m P v₀ k isLong hρ hρr q ψ hψ)
    (small_boundary m P v₀ k isLong hρ hρr q ψ hψ hm hρ1)

theorem primitive_carrier_zero (C : Set (localSpace P v₀ k))
    (hΦ : cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) C) (m + q + 1)
      (original m P v₀ k isLong hρ hρr q ψ) = 0)
    (hχ : cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) C) (m + q)
      (proposed m P v₀ k isLong hρ hρr q ψ hm hρ1) = 0) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) C) (m + q)
      (primitive m P v₀ k isLong hρ hρr q ψ hm hρ1) = 0 :=
  SmallChainPrimitiveCorrection.primitive_support_zero (sourceCover m P v₀ k isLong ρ r) (m + q) _ _ C hΦ hχ

end
end Finsler.NativeSameLegSupportedPrimitive
