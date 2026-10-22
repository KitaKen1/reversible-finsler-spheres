module

public import Finsler.Topology.SupportedCapNaturality

/-! Restriction-zero cochains vanish after every genuine family
whose entire image lies in that SAME carrier. -/
@[expose] public section
namespace Finsler.CochainCarrierPullbackZero
open CategoryTheory SphereOddDegree
open Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem family_zero {X Y : TopCat.{0}} (C : Set X) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainPullback (SupportedCap.subspaceMap X C) n φ = 0)
    (f : Y ⟶ X) (hf : ∀ y, f y ∈ C) : cochainPullback f n φ = 0 := by
  let g : Y ⟶ TopCat.of C := TopCat.ofHom ⟨fun y => ⟨f y, hf y⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ SupportedCap.subspaceMap X C := by ext y : 1; rfl
  rw [he, pullback_comp, hφ]
  exact map_zero _

end
end Finsler.CochainCarrierPullbackZero
