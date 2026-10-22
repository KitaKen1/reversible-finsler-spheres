module

public import Finsler.Loop.CapComponentRegradedSource

/-! Explicit cochain input-degree transports commute with actual
pullback and cap, also after the real small-chain inclusion. -/

@[expose] public section
namespace Finsler.CochainInputRegrade

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedCapNaturality

noncomputable section
set_option autoImplicit false

def regrade (X : TopCat.{0}) (a d : ℕ) (h : a = d)
    (φ : singularCochainGroup (ZMod 2) X d) : singularCochainGroup (ZMod 2) X a :=
  eqToHom (congrArg (chains X).X h) ≫ φ

theorem regrade_refl (X : TopCat.{0}) (a : ℕ) (φ : singularCochainGroup (ZMod 2) X a) :
    regrade X a a rfl φ = φ := by
  exact Category.id_comp φ

theorem pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (a d : ℕ) (h : a = d)
    (φ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f a (regrade Y a d h φ) = regrade X a d h (cochainPullback f d φ) := by
  cases h
  rw [regrade_refl, regrade_refl]

theorem cap (X : TopCat.{0}) (a d q : ℕ) (h : a = d)
    (φ : singularCochainGroup (ZMod 2) X d) :
    absoluteChain X a q (a + q) rfl (regrade X a d h φ) =
      eqToHom (congrArg (chains X).X (congrArg (fun n => n + q) h)) ≫
        absoluteChain X d q (d + q) rfl φ := by
  cases h
  rw [regrade_refl]
  simp only [eqToHom_refl, Category.id_comp]

theorem small_cap {X : TopCat.{0}} {ι : Type*} (U : ι → Set X) (a d q : ℕ) (h : a = d)
    (φ : singularCochainGroup (ZMod 2) X d) :
    (inclusion X U).f (a + q) ≫ absoluteChain X a q (a + q) rfl (regrade X a d h φ) =
      eqToHom (congrArg (small X U).X (congrArg (fun n => n + q) h)) ≫
        (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl φ := by
  cases h
  rw [regrade_refl]
  simp only [eqToHom_refl, Category.id_comp]

end
end Finsler.CochainInputRegrade
