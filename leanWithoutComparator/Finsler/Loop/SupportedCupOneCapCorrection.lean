module

public import Finsler.Loop.SupportedExactThomCap
public import Finsler.Loop.SupportedCapCochainCongruence
public import Finsler.Loop.SupportedCutCochainCarrierZero
public import Finsler.Loop.CupCapOrder

/-! The ACTUAL cup-one primitive of test/Thom commutation is supported
where the ORIGINAL Thom cocycle is supported. Capping it with the REAL
supported cut and a closed near cochain gives an EXPLICIT global
boundary between the two genuine cup orders. Independent carrier zeros
are preserved before any relative or time comparison is claimed. -/
@[expose] public section
namespace Finsler.SupportedCupOneCapCorrection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1050000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (a b q : ℕ)
  (α : singularCochainGroup (ZMod 2) X a) (θ : singularCochainGroup (ZMod 2) X (b + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (b + 1) θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

def kappa : singularCochainGroup (ZMod 2) X (a + b) :=
  CupOne.cupOne X a (b + 1) (a + b) (by omega) α θ

include hs in
theorem kappa_supported : cochainPullback (SupportedCap.subspaceMap X A) (a + b) (kappa X a b α θ) = 0 :=
  CupOne.restriction_zero (SupportedCap.subspaceMap X A) a (b + 1) (a + b) (by omega) α θ (Or.inr hs)

include hs in
theorem left_supported : cochainPullback (SupportedCap.subspaceMap X A) (a + b + 1)
    (CupOne.cup X a (b + 1) (a + b + 1) (by omega) α θ) = 0 :=
  CupCapOrder.restriction_zero (SupportedCap.subspaceMap X A) a (b + 1) _ (by omega) α θ (Or.inr hs)

include hs in
theorem right_supported : cochainPullback (SupportedCap.subspaceMap X A) (a + b + 1)
    (CupOne.cup X (b + 1) a (a + b + 1) (by omega) θ α) = 0 :=
  CupCapOrder.restriction_zero (SupportedCap.subspaceMap X A) (b + 1) a _ (by omega) θ α (Or.inl hs)

include hs in
theorem difference_supported : cochainPullback (SupportedCap.subspaceMap X A) (a + b + 1)
    (CupOne.cup X a (b + 1) (a + b + 1) (by omega) α θ -
      CupOne.cup X (b + 1) a (a + b + 1) (by omega) θ α) = 0 := by
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X A).op).f (a + b + 1)).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((left_supported X A a b α θ hs).trans (right_supported X A a b α θ hs).symm)

def left : singularCochainGroup (ZMod 2) X ((a + b) + q + 1) :=
  SupportedCap.cut X A B hA hB hc (a + b + 1) q ((a + b) + q + 1) (by omega)
    (CupOne.cup X a (b + 1) (a + b + 1) (by omega) α θ) (left_supported X A a b α θ hs) ≫ ψ

def right : singularCochainGroup (ZMod 2) X ((a + b) + q + 1) :=
  SupportedCap.cut X A B hA hB hc (a + b + 1) q ((a + b) + q + 1) (by omega)
    (CupOne.cup X (b + 1) a (a + b + 1) (by omega) θ α) (right_supported X A a b α θ hs) ≫ ψ

def correction : singularCochainGroup (ZMod 2) X ((a + b) + q) :=
  SupportedExactThomCap.correction X A B hA hB hc (a + b) (kappa X a b α θ)
    (kappa_supported X A a b α θ hs) q ψ

theorem kappa_boundary (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0) :
    cochainCoboundary (ZMod 2) X (a + b) (kappa X a b α θ) =
      CupOne.cup X a (b + 1) (a + b + 1) (by omega) α θ -
        CupOne.cup X (b + 1) a (a + b + 1) (by omega) θ α :=
  CupOne.boundary_cocycles X a (b + 1) (a + b) (by omega) α θ hα hθ

theorem correction_boundary (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (correction X A B hA hB hc a b q α θ hs ψ) =
      left X A B hA hB hc a b q α θ hs ψ - right X A B hA hB hc a b q α θ hs ψ := by
  have he := SupportedExactThomCap.correction_boundary X A B hA hB hc (a + b) (kappa X a b α θ)
    (kappa_supported X A a b α θ hs) q ψ hψ
  have hcut := SupportedCapCochainCongruence.cut_eq X A B hA hB hc (a + b + 1) q ((a + b) + q + 1) (by omega)
    (cochainCoboundary (ZMod 2) X (a + b) (kappa X a b α θ))
    (CupOne.cup X a (b + 1) (a + b + 1) (by omega) α θ - CupOne.cup X (b + 1) a (a + b + 1) (by omega) θ α)
    (SupportedExactThomCap.coboundary_supported X A (a + b) _ (kappa_supported X A a b α θ hs))
    (difference_supported X A a b α θ hs) (kappa_boundary X a b α θ hα hθ)
  exact he.trans ((congrArg (fun f => f ≫ ψ) hcut).trans (by
    rw [SupportedCapCochain.cut_sub X A B hA hB hc _ q _ _ _ _
      (left_supported X A a b α θ hs) (right_supported X A a b α θ hs) (difference_supported X A a b α θ hs),
      Preadditive.sub_comp]
    rfl))

theorem correction_carrier_zero (C : Set X)
    (hψC : cochainPullback (restriction (SupportedCap.subspaceMap X C)
      ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) _ (correction X A B hA hB hc a b q α θ hs ψ) = 0 :=
  SupportedCutCochainCarrierZero.subspace_cochain_zero X A B C hA hB hc (a + b) q _
    (kappa_supported X A a b α θ hs) ψ hψC

end
end Finsler.SupportedCupOneCapCorrection
