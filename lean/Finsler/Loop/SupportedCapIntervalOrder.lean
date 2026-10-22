module

public import Finsler.Loop.SupportedCapIntervalLocal
public import Finsler.Loop.SupportedIntervalFaces

/-! Interchange of the actual supported Thom cap with the genuine
right interval, tested by a closed cochain vanishing at BOTH endpoints.
ONE original subdivision prism gives the full scalar coboundary.
The primitive retains literal vanishing on every Thom-zero carrier. -/
@[expose] public section
namespace Finsler.SupportedCapIntervalOrder
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RightIntervalCochain Finsler.SupportedCapIntervalLocal
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (p q : ℕ)
  (θ : singularCochainGroup (ZMod 2) X (p + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (p + 1) θ = 0)
  (T : singularCochainGroup (ZMod 2) (space (TopCat.of B)) (q + 1))

def primitive : singularCochainGroup (ZMod 2) X (p + q) :=
  SupportedSmallCochainComparison.primitive (SupportedCap.cover X A B) (p + q)
    (difference X A B hA hB hc p q θ hs T)

variable (hθ : cochainCoboundary (ZMod 2) X (p + 1) θ = 0)
  (hT : cochainCoboundary (ZMod 2) (space (TopCat.of B)) (q + 1) T = 0)
  (h₀ : cochainPullback (endpoint (TopCat.of B) 0) (q + 1) T = 0)
  (h₁ : cochainPullback (endpoint (TopCat.of B) 1) (q + 1) T = 0)

include hθ hT h₀ h₁ in
theorem before_closed : cochainCoboundary (ZMod 2) X (p + q + 1)
    (before X A B hA hB hc p q θ hs T) = 0 :=
  SupportedCapTestOrderCoupling.supported_closed X A B hA hB hc (p + 1) q (p + q + 1)
    (by omega) θ hs hθ _ (integration_closed (TopCat.of B) q T hT h₀ h₁)

include hθ hT h₀ h₁ in
theorem after_closed : cochainCoboundary (ZMod 2) X (p + q + 1)
    (after X A B hA hB hc p q θ hs T) = 0 :=
  integration_closed X (p + q + 1) _
    (SupportedIntervalProduct.tested_closed X A B hA hB hc (p + 1) (q + 1) _ (by omega) θ hs T hθ hT)
    (SupportedIntervalFaces.tested_endpoint_zero X A B hA hB hc (p + 1) (q + 1) _ (by omega) θ hs T 0 h₀)
    (SupportedIntervalFaces.tested_endpoint_zero X A B hA hB hc (p + 1) (q + 1) _ (by omega) θ hs T 1 h₁)

include hθ hT h₀ h₁ in
theorem difference_closed : cochainCoboundary (ZMod 2) X (p + q + 1)
    (difference X A B hA hB hc p q θ hs T) = 0 := by
  change ((cochainCxZMod2 X).d _ _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_closed X A B hA hB hc p q θ hs T hθ hT h₀ h₁).trans
    (after_closed X A B hA hB hc p q θ hs T hθ hT h₀ h₁).symm)

include hθ hT h₀ h₁ in
theorem boundary (hnorm : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) θ) :
    cochainCoboundary (ZMod 2) X (p + q) (primitive X A B hA hB hc p q θ hs T) =
      before X A B hA hB hc p q θ hs T - after X A B hA hB hc p q θ hs T :=
  SupportedSmallCochainComparison.primitive_boundary (SupportedCap.cover X A B)
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hc) (p + q) _
    (difference_closed X A B hA hB hc p q θ hs T hθ hT h₀ h₁)
    (small_equal X A B hA hB hc p q θ hs T hnorm)

include hθ hT h₀ h₁ in
theorem cycle_values_eq (hnorm : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) θ)
    (c : coeff ⟶ (chains X).X (p + q + 1))
    (hcy : c ≫ (chains X).d (p + q + 1) (p + q) = 0) :
    c ≫ before X A B hA hB hc p q θ hs T = c ≫ after X A B hA hB hc p q θ hs T := by
  have h := congrArg (fun z => c ≫ z) (boundary X A B hA hB hc p q θ hs T hθ hT h₀ h₁ hnorm)
  change c ≫ ((chains X).d (p + q + 1) (p + q) ≫ primitive X A B hA hB hc p q θ hs T) = _ at h
  rw [← Category.assoc c, hcy, zero_comp, Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

theorem before_thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) (p + 1) θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) (p + q + 1)
      (before X A B hA hB hc p q θ hs T) = 0 :=
  SupportedRightTestLocal.cut_thom_zero X A B S hA hB hc (p + 1) q (p + q + 1) (by omega)
    θ hs hS (TimeTriangleSplit.interval (TopCat.of B) q ≫ T)

theorem after_thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) (p + 1) θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) (p + q + 1)
      (after X A B hA hB hc p q θ hs T) = 0 := by
  change (push (SupportedCap.subspaceMap X S)).f _ ≫ (TimeTriangleSplit.interval X _ ≫ _) = 0
  rw [← Category.assoc, RightIntervalCochain.naturality, Category.assoc]
  have h := SupportedIntervalFaces.tested_thom_zero X A B hA hB hc (p + 1) (q + 1)
    (p + q + 1 + 1) (by omega) θ hs T S hS
  change (push (SupportedCap.subspaceMap X S ▷ TopCat.I)).f (p + q + 1 + 1) ≫
    SupportedIntervalProduct.tested X A B hA hB hc (p + 1) (q + 1) (p + q + 1 + 1)
      (by omega) θ hs T = 0 at h
  rw [h, comp_zero]

theorem primitive_thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) (p + 1) θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) (p + q) (primitive X A B hA hB hc p q θ hs T) = 0 := by
  apply SupportedSmallCochainComparison.primitive_support_zero
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_thom_zero X A B hA hB hc p q θ hs T S hS).trans
    (after_thom_zero X A B hA hB hc p q θ hs T S hS).symm)

end
end Finsler.SupportedCapIntervalOrder
