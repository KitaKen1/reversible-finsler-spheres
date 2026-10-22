module

public import Finsler.Loop.CupCapOrder
public import Finsler.Loop.SupportedCapSmallNaturality
public import Finsler.Topology.SmallCapCarrier

/-! EXACT localized test/Thom order identities on the ORIGINAL small
chain cover. Absolute cap preserves that SAME cover. The actual near
inclusion is mono on chains, so both identities retain the real localized
maps and every source-degree transport, without closure assumptions. -/
@[expose] public section
namespace Finsler.SupportedCapTestOrderLocal
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000

variable (X : TopCat.{0}) (A B : Set X) (a b : ℕ)
  (α : singularCochainGroup (ZMod 2) X a) (θ : singularCochainGroup (ZMod 2) X b)
  (hs : cochainPullback (SupportedCap.subspaceMap X A) b θ = 0)

include hs in
theorem before_supported : cochainPullback (SupportedCap.subspaceMap X A) (a + b)
    (CupOne.cup X a b (a + b) rfl α θ) = 0 :=
  CupCapOrder.restriction_zero (SupportedCap.subspaceMap X A) a b (a + b) rfl α θ (Or.inr hs)

include hs in
theorem after_supported : cochainPullback (SupportedCap.subspaceMap X A) (a + b)
    (CupOne.cup X b a (a + b) (by omega) θ α) = 0 :=
  CupCapOrder.restriction_zero (SupportedCap.subspaceMap X A) b a (a + b) (by omega) θ α (Or.inl hs)

theorem before_localized (q : ℕ) :
    SmallCapCarrier.smallCap X (SupportedCap.cover X A B) a (b + q) ((a + b) + q) (by omega) α ≫
      SupportedCap.localizedCap X A B b q (b + q) rfl θ hs =
    SupportedCap.localizedCap X A B (a + b) q ((a + b) + q) rfl
      (CupOne.cup X a b (a + b) rfl α θ) (before_supported X A a b α θ hs) := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  change (_ ≫ _) ≫ (push (SupportedCap.subspaceMap X B)).f q = _
  calc
    _ = SmallCapCarrier.smallCap X (SupportedCap.cover X A B) a (b + q) ((a + b) + q) (by omega) α ≫
        (inclusion X (SupportedCap.cover X A B)).f (b + q) ≫ absoluteChain X b q (b + q) rfl θ := by
      simpa only [push, Category.assoc] using congrArg
        (fun f => SmallCapCarrier.smallCap X (SupportedCap.cover X A B) a (b + q) ((a + b) + q) (by omega) α ≫ f)
        (SupportedCap.localizedCap_inclusion X A B b q (b + q) rfl θ hs)
    _ = (inclusion X (SupportedCap.cover X A B)).f ((a + b) + q) ≫
        absoluteChain X a (b + q) ((a + b) + q) (by omega) α ≫ absoluteChain X b q (b + q) rfl θ := by
      rw [← Category.assoc, SmallCapCarrier.smallCap_inclusion, Category.assoc]
    _ = (inclusion X (SupportedCap.cover X A B)).f ((a + b) + q) ≫
        absoluteChain X (a + b) q ((a + b) + q) rfl (CupOne.cup X a b (a + b) rfl α θ) := by
      rw [CupCapOrder.cap_cup X a b (a + b) q rfl α θ]
    _ = _ := (SupportedCap.localizedCap_inclusion X A B (a + b) q ((a + b) + q) rfl _ _).symm

theorem after_localized (q : ℕ) :
    SupportedCap.localizedCap X A B b (a + q) ((a + b) + q) (by omega) θ hs ≫
      absoluteChain (TopCat.of B) a q (a + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) a α) =
    SupportedCap.localizedCap X A B (a + b) q ((a + b) + q) rfl
      (CupOne.cup X b a (a + b) (by omega) θ α) (after_supported X A a b α θ hs) := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  change (_ ≫ _) ≫ (push (SupportedCap.subspaceMap X B)).f q = _
  calc
    _ = SupportedCap.localizedCap X A B b (a + q) ((a + b) + q) (by omega) θ hs ≫
        (push (SupportedCap.subspaceMap X B)).f (a + q) ≫ absoluteChain X a q (a + q) rfl α := by
      simpa only [push, Category.assoc] using congrArg
        (fun f => SupportedCap.localizedCap X A B b (a + q) ((a + b) + q) (by omega) θ hs ≫ f)
        (RelativeCapBoundary.absolute_chain_natural (SupportedCap.subspaceMap X B) a q (a + q) rfl α)
    _ = (inclusion X (SupportedCap.cover X A B)).f ((a + b) + q) ≫
        absoluteChain X b (a + q) ((a + b) + q) (by omega) θ ≫ absoluteChain X a q (a + q) rfl α := by
      simpa only [push, Category.assoc] using congrArg
        (fun f => f ≫ absoluteChain X a q (a + q) rfl α)
        (SupportedCap.localizedCap_inclusion X A B b (a + q) ((a + b) + q) (by omega) θ hs)
    _ = (inclusion X (SupportedCap.cover X A B)).f ((a + b) + q) ≫
        absoluteChain X (a + b) q ((a + b) + q) rfl (CupOne.cup X b a (a + b) (by omega) θ α) := by
      rw [CupCapOrder.cap_cup X b a (a + b) q (by omega) θ α]
    _ = _ := (SupportedCap.localizedCap_inclusion X A B (a + b) q ((a + b) + q) rfl _ _).symm


theorem before_at_degree (q N : ℕ) (hN : (a + b) + q = N) :
    SmallCapCarrier.smallCap X (SupportedCap.cover X A B) a (b + q) N (by omega) α ≫
      SupportedCap.localizedCap X A B b q (b + q) rfl θ hs =
    SupportedCap.localizedCap X A B (a + b) q N hN (CupOne.cup X a b (a + b) rfl α θ)
      (before_supported X A a b α θ hs) := by
  subst N
  exact before_localized X A B a b α θ hs q

theorem after_at_degree (q N : ℕ) (hN : (a + b) + q = N) :
    SupportedCap.localizedCap X A B b (a + q) N (by omega) θ hs ≫
      absoluteChain (TopCat.of B) a q (a + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) a α) =
    SupportedCap.localizedCap X A B (a + b) q N hN (CupOne.cup X b a (a + b) (by omega) θ α)
      (after_supported X A a b α θ hs) := by
  subst N
  exact after_localized X A B a b α θ hs q

end
end Finsler.SupportedCapTestOrderLocal
