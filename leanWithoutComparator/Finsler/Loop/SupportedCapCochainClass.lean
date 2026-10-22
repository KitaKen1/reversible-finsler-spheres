module

public import Finsler.Loop.SupportedSmallCochainComparison
public import Finsler.Loop.SupportedCapSmallNaturality
public import Finsler.Topology.RelativeCapDual
public import Finsler.Loop.DegreeLoweringCochainPullback

/-! The REAL supported first cap followed by a GLOBAL cochain has
the actual ordinary cup class. Exact small-input equality and the
original subdivision-prism primitive prove the cochain comparison. -/
@[expose] public section
namespace Finsler.SupportedCapCochainClass
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem class_eq_of_small {X : TopCat.{0}} {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ) (N : ℕ) (hN : 1 ≤ N)
    (φ ψ : singularCochainGroup (ZMod 2) X N)
    (hφ : cochainCoboundary (ZMod 2) X N φ = 0) (hψ : cochainCoboundary (ZMod 2) X N ψ = 0)
    (he : (SmallChainCarrier.inclusion X U).f N ≫ φ = (SmallChainCarrier.inclusion X U).f N ≫ ψ) :
    CochainClass.classOf (cochainCxZMod2 X) N φ hφ = CochainClass.classOf (cochainCxZMod2 X) N ψ hψ := by
  cases N with
  | zero => omega
  | succ n =>
    have hδ : cochainCoboundary (ZMod 2) X (n + 1) (φ - ψ) = 0 := by
      change ((cochainCxZMod2 X).d (n + 1) (n + 2)).hom (φ - ψ) = 0
      rw [map_sub]
      change cochainCoboundary (ZMod 2) X (n + 1) φ - cochainCoboundary (ZMod 2) X (n + 1) ψ = 0
      rw [hφ, hψ, sub_self]
    have hs : (SmallChainCarrier.inclusion X U).f (n + 1) ≫ (φ - ψ) = 0 := by
      rw [Preadditive.comp_sub, he, sub_self]
    exact RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 X) n (n + 1)
      (SupportedSmallCochainComparison.primitive U n (φ - ψ)) φ ψ hφ hψ
      (SupportedSmallCochainComparison.primitive_boundary U hU hc n (φ - ψ) hδ hs).symm

theorem supported_cap_cup (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q : ℕ) (hpq : 1 ≤ p + q)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cocycleClass X (p + q)
      ((SupportedCapHomology.operation X A B hA hB hc p φ hs hφ).component q ≫
        cochainPullback (SupportedCap.subspaceMap X B) q ψ)
      (DegreeLoweringCochainPullback.closed _ q _ (cochainPullback_cocycle _ q ψ hψ)) =
      cupZMod2 (cocycleClass X p φ hφ) (cocycleClass X q ψ hψ) := by
  have hl := DegreeLoweringCochainPullback.closed
    (SupportedCapHomology.operation X A B hA hB hc p φ hs hφ) q _
    (cochainPullback_cocycle (SupportedCap.subspaceMap X B) q ψ hψ)
  have hr := cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ
  have he : (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
      ((SupportedCapHomology.operation X A B hA hB hc p φ hs hφ).component q ≫
        cochainPullback (SupportedCap.subspaceMap X B) q ψ) =
      (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫ cochainCup p q φ ψ := by
    change _ ≫ (SupportedCap.cut X A B hA hB hc p q (p + q) rfl φ hs ≫
      ((push (SupportedCap.subspaceMap X B)).f q ≫ ψ)) = _
    rw [← Category.assoc, ← Category.assoc, SupportedCapSmallNaturality.small_input]
    have hi : SupportedCap.localizedCap X A B p q (p + q) rfl φ hs ≫
        (push (SupportedCap.subspaceMap X B)).f q =
        (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
          RelativeCapAssociativity.absoluteChain X p q (p + q) rfl φ :=
      SupportedCap.localizedCap_inclusion X A B p q (p + q) rfl φ hs
    exact (congrArg (fun a => a ≫ ψ) hi).trans
      ((Category.assoc _ _ _).trans (congrArg
        (fun a => (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫ a)
        (RelativeCapDual.absolute_chain_dual X p q φ ψ)))
  have hclass := class_eq_of_small (SupportedCap.cover X A B) (SupportedCap.cover_open X A B hA hB)
    (SupportedCap.cover_univ X A B hc) (p + q) hpq _ _ hl hr he
  exact hclass.trans (cupZMod2_mk φ hφ ψ hψ).symm

end
end Finsler.SupportedCapCochainClass
