module

public import Finsler.Loop.SupportedCapNearRestriction
public import Finsler.Loop.SupportedCapTestOrderCoupling
public import Finsler.Loop.SupportedThomCarrierZero

/-! Right evaluation needs only strict AW associativity on the SAME
near/far cover. The actual small approximation is fixed on near chains.
No cup-one correction or naturality of a chosen retraction is assumed. -/
@[expose] public section
namespace Finsler.SupportedRightTestLocal
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

theorem dual_at_degree (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    absoluteChain X p q N h φ ≫ ψ = CupOne.cup X p q N h φ ψ := by
  subst N
  exact (RelativeCapDual.absolute_chain_dual X p q φ ψ).trans (CupOne.cup_comparison X p q φ ψ).symm

theorem cup_assoc (X : TopCat.{0}) (p q r d e N : ℕ)
    (hd : p + q = d) (he : q + r = e) (hN : d + r = N) (hN' : p + e = N)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (α : singularCochainGroup (ZMod 2) X r) :
    CupOne.cup X d r N hN (CupOne.cup X p q d hd φ ψ) α =
      CupOne.cup X p e N hN' φ (CupOne.cup X q r e he ψ α) := by
  subst d e N
  have hh := congrArg (fun f => f ≫ α) (CupCapOrder.cap_cup X p q (p + q) r rfl φ ψ)
  simp only [Category.assoc, dual_at_degree] at hh
  exact hh.symm

theorem cut_near_scalar (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    cochainPullback (SupportedCap.subspaceMap X B) N (SupportedCap.cut X A B hA hB hc p q N hN θ hs ≫ ψ) =
      CupOne.cup (TopCat.of B) p q N hN (cochainPullback (SupportedCap.subspaceMap X B) p θ) ψ := by
  change (push (SupportedCap.subspaceMap X B)).f N ≫ (_ ≫ ψ) = _
  rw [← Category.assoc, SupportedCapNearRestriction.cut_near, dual_at_degree]

theorem cut_thom_zero (X : TopCat.{0}) (A B S : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    cochainPullback (SupportedCap.subspaceMap X S) N (SupportedCap.cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0 := by
  have hz := congrArg (fun f => f ≫ ψ) (SupportedThomCarrierZero.cut_map_zero A B S hA hB hc
    p q N hN θ hs hS (SupportedCap.subspaceMap X S) (fun z => z.property))
  simp only [Category.assoc, zero_comp] at hz
  exact hz

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (a b q : ℕ)
  (α : singularCochainGroup (ZMod 2) X a) (θ : singularCochainGroup (ZMod 2) X (b + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (b + 1) θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

def cutTest : singularCochainGroup (ZMod 2) X ((b + 1) + q) :=
  SupportedCap.cut X A B hA hB hc (b + 1) q ((b + 1) + q) rfl θ hs ≫ ψ

def before : singularCochainGroup (ZMod 2) X ((b + q) + a + 1) :=
  CupOne.cup X ((b + 1) + q) a ((b + q) + a + 1) (by omega)
    (cutTest X A B hA hB hc b q θ hs ψ) α

def after : singularCochainGroup (ZMod 2) X ((b + q) + a + 1) :=
  SupportedCap.cut X A B hA hB hc (b + 1) (q + a) ((b + q) + a + 1) (by omega) θ hs ≫
    CupOne.cup (TopCat.of B) q a (q + a) rfl ψ (cochainPullback (SupportedCap.subspaceMap X B) a α)

theorem near_equal : cochainPullback (SupportedCap.subspaceMap X B) _ (before X A B hA hB hc a b q α θ hs ψ) =
    cochainPullback (SupportedCap.subspaceMap X B) _ (after X A B hA hB hc a b q α θ hs ψ) := by
  unfold before after cutTest
  rw [CupCapOrder.naturality, cut_near_scalar, cut_near_scalar]
  exact cup_assoc (TopCat.of B) (b + 1) q a ((b + 1) + q) (q + a) ((b + q) + a + 1)
    rfl rfl (by omega) (by omega) _ ψ _

theorem before_thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) (b + 1) θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) _ (before X A B hA hB hc a b q α θ hs ψ) = 0 :=
  CupCapOrder.restriction_zero (SupportedCap.subspaceMap X S) ((b + 1) + q) a _ (by omega) _ α
    (Or.inl (cut_thom_zero X A B S hA hB hc (b + 1) q _ rfl θ hs hS ψ))

theorem after_thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) (b + 1) θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) _ (after X A B hA hB hc a b q α θ hs ψ) = 0 :=
  cut_thom_zero X A B S hA hB hc (b + 1) (q + a) _ (by omega) θ hs hS _

def difference : singularCochainGroup (ZMod 2) X ((b + q) + a + 1) :=
  before X A B hA hB hc a b q α θ hs ψ - after X A B hA hB hc a b q α θ hs ψ

theorem small_equal : (inclusion X (SupportedCap.cover X A B)).f ((b + q) + a + 1) ≫
    difference X A B hA hB hc a b q α θ hs ψ = 0 := by
  apply CarrierCochainZero.small_zero
  intro i
  cases i with
  | false =>
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X A).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((before_thom_zero X A B hA hB hc a b q α θ hs ψ A hs).trans
      (after_thom_zero X A B hA hB hc a b q α θ hs ψ A hs).symm)
  | true =>
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X B).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (near_equal X A B hA hB hc a b q α θ hs ψ)

end
end Finsler.SupportedRightTestLocal
