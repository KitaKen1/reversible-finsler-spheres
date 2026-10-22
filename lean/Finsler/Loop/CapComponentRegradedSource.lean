module

public import Finsler.Loop.LocalizedCapCupComponentSource

/-! The actual source of a localized cap after an arbitrary input
component and an explicit source-degree transport. -/

@[expose] public section
namespace Finsler.CapComponentRegradedSource

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

theorem input_transport (X : TopCat.{0}) (d q N M : ℕ) (hN : d + q = N) (hM : d + q = M)
    (hNM : N = M) (φ : singularCochainGroup (ZMod 2) X d) :
    eqToHom (congrArg (chains X).X hNM) ≫ absoluteChain X d q M hM φ = absoluteChain X d q N hN φ := by
  cases hNM
  simp only [eqToHom_refl, Category.id_comp]

theorem source {X : TopCat.{0}} {ι : Type*} (U : ι → Set X)
    {K : ModuleCat.{0} (ZMod 2)} {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (j : E ⟶ chains X) (d q N : ℕ) (hN : N = d + q)
    (φ : singularCochainGroup (ZMod 2) X d) (f : K ⟶ (small X U).X N)
    (c : (small X U).X (d + q) ⟶ E.X q)
    (hc : c ≫ j.f q = (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl φ) :
    (f ≫ eqToHom (congrArg (small X U).X hN) ≫ c) ≫ j.f q =
      f ≫ (inclusion X U).f N ≫ absoluteChain X d q N hN.symm φ := by
  simp only [Category.assoc]
  rw [hc, ← Category.assoc (eqToHom _),
    LocalizedCapCupComponentSource.transport_f (inclusion X U) N (d + q) hN, Category.assoc,
    input_transport X d q N (d + q) hN.symm rfl hN]

end
end Finsler.CapComponentRegradedSource
