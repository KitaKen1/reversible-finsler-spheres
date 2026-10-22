module

public import Finsler.Topology.SupportedCapNaturality

/-! Exact naturality of the ORIGINAL supported cap on actual source
small chains. The pinned TauCeti retraction is STRICTLY the identity
on small chains; no naturality of the chosen retraction is assumed. -/
@[expose] public section
namespace Finsler.SupportedCapSmallNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem small_input (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (subspaceMap X A) p φ = 0) :
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
      cut X A B hA hB hc p q (p + q) rfl φ hs = localizedCap X A B p q (p + q) rfl φ hs := by
  change (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
    ((TauCeti.smallSingularRetraction coeff (SupportedCap.cover X A B)
      (cover_open X A B hA hB) (cover_univ X A B hc)).f (p + q) ≫ _) = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f, TauCeti.ι_comp_smallSingularRetraction,
    HomologicalComplex.id_f, Category.id_comp]

theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hcX : A ∪ B = Set.univ)
    (hC : IsOpen C) (hD : IsOpen D) (hcY : C ∪ D = Set.univ)
    (hfA : Set.MapsTo f A C) (hfB : Set.MapsTo f B D)
    (p q : ℕ) (φ : singularCochainGroup (ZMod 2) Y p)
    (hs : cochainPullback (subspaceMap Y C) p φ = 0) :
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫ (push f).f (p + q) ≫
      cut Y C D hC hD hcY p q (p + q) rfl φ hs =
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
      cut X A B hA hB hcX p q (p + q) rfl (cochainPullback f p φ)
        (pullback_support f A C hfA p φ hs) ≫ (push (restriction f B D hfB)).f q := by
  have hm := smallMap_inclusion f A B C D hfA hfB
  have hi : (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫ (push f).f (p + q) =
      (smallMap f A B C D hfA hfB).f (p + q) ≫
        (SmallChainCarrier.inclusion Y (SupportedCap.cover Y C D)).f (p + q) :=
    (congrArg (fun a => a.f (p + q)) hm).symm
  calc
    _ = ((SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫ (push f).f (p + q)) ≫
        cut Y C D hC hD hcY p q (p + q) rfl φ hs := by rw [Category.assoc]
    _ = (smallMap f A B C D hfA hfB).f (p + q) ≫ localizedCap Y C D p q (p + q) rfl φ hs := by
      rw [hi, Category.assoc, small_input]
    _ = localizedCap X A B p q (p + q) rfl (cochainPullback f p φ)
        (pullback_support f A C hfA p φ hs) ≫ (push (restriction f B D hfB)).f q :=
      localized_naturality f A B C D hfA hfB p q (p + q) rfl φ hs
    _ = _ := by rw [← Category.assoc, small_input]

end
end Finsler.SupportedCapSmallNaturality
