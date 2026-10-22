module

public import Finsler.Loop.SupportedCapCochainCongruence
public import Finsler.Loop.NativeSuffixPostponedAlignment

/-! Transport an actual supported cap across equal open sets. The
near test is pulled along the actual identity-on-points map; both
support witnesses and the source degree are retained. -/
@[expose] public section
namespace Finsler.SupportedCapSetTransport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false

def nearMap (X : TopCat.{0}) (B D : Set X) (h : B = D) : TopCat.of B ⟶ TopCat.of D :=
  TopCat.ofHom ⟨fun z => ⟨z.val, h ▸ z.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem nearMap_self (X : TopCat.{0}) (B : Set X) (h : B = B) :
    nearMap X B B h = 𝟙 (TopCat.of B) := rfl

theorem nearMap_inclusion (X : TopCat.{0}) (B D : Set X) (h : B = D) :
    nearMap X B D h ≫ SupportedCap.subspaceMap X D = SupportedCap.subspaceMap X B := rfl

theorem scalar (X : TopCat.{0}) (A B C D : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hD : IsOpen D)
    (hAB : A ∪ B = Set.univ) (hCD : C ∪ D = Set.univ)
    (hAC : A = C) (hBD : B = D) (p q N : ℕ) (hN : p + q = N)
    (θ η : singularCochainGroup (ZMod 2) X p)
    (hθ : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (hη : cochainPullback (SupportedCap.subspaceMap X C) p η = 0)
    (he : θ = η) (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q) :
    SupportedCap.cut X A B hA hB hAB p q N hN θ hθ ≫
      cochainPullback (nearMap X B D hBD) q ψ =
    SupportedCap.cut X C D hC hD hCD p q N hN η hη ≫ ψ := by
  subst C D η
  rw [nearMap_self]
  change _ ≫ ((push (𝟙 (TopCat.of B))).f q ≫ ψ) = _
  simp only [push, CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
  change _ ≫ (𝟙 _ ≫ ψ) = _
  rw [Category.id_comp]
  rfl

end
end Finsler.SupportedCapSetTransport
