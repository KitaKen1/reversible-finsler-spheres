module

public import Finsler.Topology.SmallTensorHomologyCancellation

/-! Transport actual homology cross products and actual chain-map
homology along equality of total degrees. -/

@[expose] public section
namespace Finsler.HomologyDegreeTransport

open CategoryTheory MonoidalCategory HomologicalComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

theorem map {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg (fun k => C.homology k) h) ≫ homologyMap f j =
      homologyMap f i ≫ eqToHom (congrArg (fun k => D.homology k) h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem cross (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i j N M : ℕ) (hN : i + j = N) (h : N = M) :
    homologyCross C D i j N hN ≫ eqToHom (congrArg (fun k => (C ⊗ D).homology k) h) =
      homologyCross C D i j M (hN.trans h) := by
  subst M
  simp only [eqToHom_refl, Category.comp_id]

end
end Finsler.HomologyDegreeTransport
