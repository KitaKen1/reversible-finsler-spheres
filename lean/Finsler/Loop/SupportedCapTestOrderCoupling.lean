module

public import Finsler.Loop.SupportedCapTestOrderLocal
public import Finsler.Loop.SupportedSmallCochainComparison
public import Finsler.Loop.DegreeLoweringCochainPullback

/-! The ACTUAL interleaved test--supported-Thom cap has an explicit
subdivision-prism boundary to the supported cap of test CUP Thom.
Thom followed by the restricted test is EXACTLY the supported cap of
Thom CUP test. All actual small retractions and degree casts remain. -/
@[expose] public section
namespace Finsler.SupportedCapTestOrderCoupling
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

theorem absolute_closed (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (α : singularCochainGroup (ZMod 2) X p) (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (β : singularCochainGroup (ZMod 2) X q) (hβ : cochainCoboundary (ZMod 2) X q β = 0) :
    cochainCoboundary (ZMod 2) X N (absoluteChain X p q N h α ≫ β) = 0 := by
  subst N
  exact DegreeLoweringCochainPullback.closed (SupportedCapHomology.absoluteOperation X p α hα) q β hβ

theorem supported_closed (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q N : ℕ) (h : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (hθ : cochainCoboundary (ZMod 2) X p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X N (SupportedCap.cut X A B hA hB hc p q N h θ hs ≫ ψ) = 0 := by
  subst N
  exact DegreeLoweringCochainPullback.closed (SupportedCapHomology.operation X A B hA hB hc p θ hs hθ) q ψ hψ

theorem small_input_at_degree (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0) :
    (inclusion X (SupportedCap.cover X A B)).f N ≫ SupportedCap.cut X A B hA hB hc p q N hN θ hs =
      SupportedCap.localizedCap X A B p q N hN θ hs := by
  subst N
  exact SupportedCapSmallNaturality.small_input X A B hA hB hc p q θ hs

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (a b q : ℕ)
  (α : singularCochainGroup (ZMod 2) X a) (θ : singularCochainGroup (ZMod 2) X (b + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (b + 1) θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

def before : singularCochainGroup (ZMod 2) X ((a + b) + q + 1) :=
  absoluteChain X a ((b + 1) + q) ((a + b) + q + 1) (by omega) α ≫
    SupportedCap.cut X A B hA hB hc (b + 1) q ((b + 1) + q) rfl θ hs ≫ ψ

def beforeCoupled : singularCochainGroup (ZMod 2) X ((a + b) + q + 1) :=
  SupportedCap.cut X A B hA hB hc (a + (b + 1)) q ((a + b) + q + 1) (by omega)
    (CupOne.cup X a (b + 1) (a + (b + 1)) rfl α θ)
    (SupportedCapTestOrderLocal.before_supported X A a (b + 1) α θ hs) ≫ ψ

def after : singularCochainGroup (ZMod 2) X ((a + b) + q + 1) :=
  SupportedCap.cut X A B hA hB hc (b + 1) (a + q) ((a + b) + q + 1) (by omega) θ hs ≫
    absoluteChain (TopCat.of B) a q (a + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) a α) ≫ ψ

def afterCoupled : singularCochainGroup (ZMod 2) X ((a + b) + q + 1) :=
  SupportedCap.cut X A B hA hB hc (a + (b + 1)) q ((a + b) + q + 1) (by omega)
    (CupOne.cup X (b + 1) a (a + (b + 1)) (by omega) θ α)
    (SupportedCapTestOrderLocal.after_supported X A a (b + 1) α θ hs) ≫ ψ

theorem before_small :
    (inclusion X (SupportedCap.cover X A B)).f ((a + b) + q + 1) ≫ before X A B hA hB hc a b q α θ hs ψ =
    (inclusion X (SupportedCap.cover X A B)).f ((a + b) + q + 1) ≫ beforeCoupled X A B hA hB hc a b q α θ hs ψ := by
  let sc := SmallCapCarrier.smallCap X (SupportedCap.cover X A B) a ((b + 1) + q) ((a + b) + q + 1) (by omega) α
  calc
    _ = sc ≫ (inclusion X (SupportedCap.cover X A B)).f ((b + 1) + q) ≫
        SupportedCap.cut X A B hA hB hc (b + 1) q ((b + 1) + q) rfl θ hs ≫ ψ := by
      simpa only [before, Category.assoc] using congrArg
        (fun k => k ≫ SupportedCap.cut X A B hA hB hc (b + 1) q ((b + 1) + q) rfl θ hs ≫ ψ)
        (SmallCapCarrier.smallCap_inclusion X (SupportedCap.cover X A B) a ((b + 1) + q) ((a + b) + q + 1) (by omega) α).symm
    _ = sc ≫ SupportedCap.localizedCap X A B (b + 1) q ((b + 1) + q) rfl θ hs ≫ ψ := by
      simpa only [Category.assoc] using congrArg (fun k => sc ≫ k ≫ ψ)
        (SupportedCapSmallNaturality.small_input X A B hA hB hc (b + 1) q θ hs)
    _ = SupportedCap.localizedCap X A B (a + (b + 1)) q ((a + b) + q + 1) (by omega)
        (CupOne.cup X a (b + 1) (a + (b + 1)) rfl α θ)
        (SupportedCapTestOrderLocal.before_supported X A a (b + 1) α θ hs) ≫ ψ := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ ψ)
        (SupportedCapTestOrderLocal.before_at_degree X A B a (b + 1) α θ hs q ((a + b) + q + 1) (by omega))
    _ = _ := by
      simpa only [beforeCoupled, Category.assoc] using congrArg (fun k => k ≫ ψ)
        (small_input_at_degree X A B hA hB hc (a + (b + 1)) q ((a + b) + q + 1) (by omega)
          (CupOne.cup X a (b + 1) (a + (b + 1)) rfl α θ)
          (SupportedCapTestOrderLocal.before_supported X A a (b + 1) α θ hs)).symm

theorem after_exact : after X A B hA hB hc a b q α θ hs ψ = afterCoupled X A B hA hB hc a b q α θ hs ψ := by
  let r := TauCeti.smallSingularRetraction coeff (SupportedCap.cover X A B)
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hc)
  have he := congrArg (fun k => r.f ((a + b) + q + 1) ≫ k ≫ ψ)
    (SupportedCapTestOrderLocal.after_at_degree X A B a (b + 1) α θ hs q ((a + b) + q + 1) (by omega))
  simpa only [after, afterCoupled, SupportedCap.cut, Category.assoc] using he

variable (hα : cochainCoboundary (ZMod 2) X a α = 0)
  (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
  (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0)

include hα hθ hψ in
theorem before_closed : cochainCoboundary (ZMod 2) X _ (before X A B hA hB hc a b q α θ hs ψ) = 0 :=
  absolute_closed X a ((b + 1) + q) _ (by omega) α hα _
    (supported_closed X A B hA hB hc (b + 1) q _ rfl θ hs hθ ψ hψ)

include hα hθ hψ in
theorem beforeCoupled_closed : cochainCoboundary (ZMod 2) X _ (beforeCoupled X A B hA hB hc a b q α θ hs ψ) = 0 :=
  supported_closed X A B hA hB hc _ q _ (by omega) _
    (SupportedCapTestOrderLocal.before_supported X A a (b + 1) α θ hs)
    (CupCapOrder.closed X a (b + 1) _ rfl α θ hα hθ) ψ hψ

include hα hθ hψ in
theorem after_closed : cochainCoboundary (ZMod 2) X _ (after X A B hA hB hc a b q α θ hs ψ) = 0 :=
  supported_closed X A B hA hB hc (b + 1) (a + q) _ (by omega) θ hs hθ _
    (absolute_closed (TopCat.of B) a q _ rfl _ (pullback_closed _ a α hα) ψ hψ)

include hα hθ hψ in
theorem afterCoupled_closed : cochainCoboundary (ZMod 2) X _ (afterCoupled X A B hA hB hc a b q α θ hs ψ) = 0 :=
  supported_closed X A B hA hB hc _ q _ (by omega) _
    (SupportedCapTestOrderLocal.after_supported X A a (b + 1) α θ hs)
    (CupCapOrder.closed X (b + 1) a _ (by omega) θ α hθ hα) ψ hψ

def difference : singularCochainGroup (ZMod 2) X ((a + b) + q + 1) :=
  before X A B hA hB hc a b q α θ hs ψ - beforeCoupled X A B hA hB hc a b q α θ hs ψ

include hα hθ hψ in
theorem difference_closed : cochainCoboundary (ZMod 2) X _ (difference X A B hA hB hc a b q α θ hs ψ) = 0 := by
  change ((cochainCxZMod2 X).d _ _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ).trans
    (beforeCoupled_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ).symm)

def primitive : singularCochainGroup (ZMod 2) X ((a + b) + q) :=
  SupportedSmallCochainComparison.primitive (SupportedCap.cover X A B) ((a + b) + q)
    (difference X A B hA hB hc a b q α θ hs ψ)

include hα hθ hψ in
theorem primitive_boundary : cochainCoboundary (ZMod 2) X _ (primitive X A B hA hB hc a b q α θ hs ψ) =
    difference X A B hA hB hc a b q α θ hs ψ := by
  apply SupportedSmallCochainComparison.primitive_boundary _
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hc)
    ((a + b) + q) _ (difference_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ)
  change _ ≫ (_ - _) = 0
  rw [Preadditive.comp_sub, before_small, sub_self]

theorem primitive_carrier_zero (C : Set X)
    (hC : cochainPullback (SupportedCap.subspaceMap X C) _ (difference X A B hA hB hc a b q α θ hs ψ) = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) _ (primitive X A B hA hB hc a b q α θ hs ψ) = 0 :=
  SupportedSmallCochainComparison.primitive_support_zero (SupportedCap.cover X A B) C _ _ hC

end
end Finsler.SupportedCapTestOrderCoupling
