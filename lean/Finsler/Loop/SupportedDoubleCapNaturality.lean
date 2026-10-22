module

public import Finsler.Topology.SupportedDoubleCap
public import Finsler.Topology.SupportedCapNaturality

/-! Genuine localized double caps commute with actual maps of both
support domains. The second cochain is pulled back on the real near
space; no global closure of its zero extension is assumed. -/

@[expose] public section
namespace Finsler.SupportedDoubleCapNaturality

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.SupportedCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem localized {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) (k p q N : ℕ) (hN : k + (p + q) = N)
    (φ : singularCochainGroup (ZMod 2) Y k)
    (hφ : cochainPullback (subspaceMap Y C) k φ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) p) :
    (smallMap f A B C D hA hB).f N ≫ SupportedDoubleCap.localized Y C D k p φ hφ ψ q N hN =
      SupportedDoubleCap.localized X A B k p (cochainPullback f k φ)
        (pullback_support f A C hA k φ hφ) (cochainPullback (restriction f B D hB) p ψ) q N hN ≫
      (push (restriction f B D hB)).f q := by
  dsimp only [SupportedDoubleCap.localized]
  rw [← Category.assoc, localized_naturality, Category.assoc]
  have hn := RelativeCapBoundary.absolute_chain_natural (restriction f B D hB) p q (p + q) rfl ψ
  change absoluteChain (TopCat.of B) p q (p + q) rfl (cochainPullback (restriction f B D hB) p ψ) ≫
    (push (restriction f B D hB)).f q =
      (push (restriction f B D hB)).f (p + q) ≫ absoluteChain (TopCat.of D) p q (p + q) rfl ψ at hn
  rw [← hn]
  simp only [Category.assoc]

end
end Finsler.SupportedDoubleCapNaturality
