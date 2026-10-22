module

public import Finsler.Topology.SupportedDoubleCap

/-! Literal naturality of the genuine localized supported double cap,
including the actual restriction of the tested cochain to the domain. -/

@[expose] public section
namespace Finsler.SupportedDoubleCapNaturality

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem localized_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A B : Set X) (C D : Set Y) (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (k p q N : ℕ) (hN : k + (p + q) = N)
    (φ : singularCochainGroup (ZMod 2) Y k)
    (hφ : cochainPullback (SupportedCap.subspaceMap Y C) k φ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) p) :
    (smallMap f A B C D hA hB).f N ≫ SupportedDoubleCap.localized Y C D k p φ hφ ψ q N hN =
      SupportedDoubleCap.localized X A B k p (cochainPullback f k φ)
        (pullback_support f A C hA k φ hφ) (cochainPullback (restriction f B D hB) p ψ) q N hN ≫
          (push (restriction f B D hB)).f q := by
  have ht := SupportedCapNaturality.localized_naturality f A B C D hA hB k (p + q) N hN φ hφ
  have hn : absoluteChain (TopCat.of B) p q (p + q) rfl
      (cochainPullback (restriction f B D hB) p ψ) ≫ (push (restriction f B D hB)).f q =
      (push (restriction f B D hB)).f (p + q) ≫ absoluteChain (TopCat.of D) p q (p + q) rfl ψ := by
    simpa only [push] using RelativeCapBoundary.absolute_chain_natural (restriction f B D hB) p q (p + q) rfl ψ
  unfold SupportedDoubleCap.localized
  rw [← Category.assoc, ht, Category.assoc, ← hn, ← Category.assoc]

end
end Finsler.SupportedDoubleCapNaturality
