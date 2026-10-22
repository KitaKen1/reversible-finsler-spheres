module

public import Finsler.Loop.SupportedCapPullbackClass
public import Finsler.Loop.CochainDegreeTransport

/-! Source-small naturality in an explicitly specified ACTUAL input
degree. This is the original cap and original small approximation;
the degree equality is transported, rather than changing the map. -/
@[expose] public section
namespace Finsler.SupportedCapSmallDegree
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
  (hA : IsOpen A) (hB : IsOpen B) (hcX : A ∪ B = Set.univ)
  (hC : IsOpen C) (hD : IsOpen D) (hcY : C ∪ D = Set.univ)
  (hfA : Set.MapsTo f A C) (hfB : Set.MapsTo f B D) (p q N : ℕ) (hN : p + q = N)
  (φ : singularCochainGroup (ZMod 2) Y p)
  (hs : cochainPullback (SupportedCap.subspaceMap Y C) p φ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q)

theorem small_equality :
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f N ≫
      cochainPullback f N (SupportedCap.cut Y C D hC hD hcY p q N hN φ hs ≫ ψ) =
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f N ≫
      (SupportedCap.cut X A B hA hB hcX p q N hN (cochainPullback f p φ)
        (pullback_support f A C hfA p φ hs) ≫ cochainPullback (restriction f B D hfB) q ψ) := by
  subst N
  exact SupportedCapPullbackClass.small_equality f A B C D hA hB hcX hC hD hcY hfA hfB p q φ hs ψ

theorem pullback_pre :
    CochainDegreeTransport.pre X hN.symm
      (cochainPullback f (p + q) (SupportedCap.cut Y C D hC hD hcY p q (p + q) rfl φ hs ≫ ψ)) =
      cochainPullback f N (SupportedCap.cut Y C D hC hD hcY p q N hN φ hs ≫ ψ) := by
  subst N
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

end
end Finsler.SupportedCapSmallDegree
