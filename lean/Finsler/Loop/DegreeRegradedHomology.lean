module

public import Finsler.Loop.DegreeLoweringRegrade

/-! Equal natural-number degree conventions transport the actual
induced homology maps, including output degree zero. -/

@[expose] public section
namespace Finsler.DegreeRegradedHomology

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

theorem homology {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f : DegreeLoweringHomology.Map C E d) (d' : ℕ) (hd : d' = d) (q : ℕ) :
    (DegreeLoweringRegrade.regrade f d' hd).homology q =
      eqToHom (congrArg (fun k => C.homology (k + q)) hd) ≫ f.homology q := by
  subst d'
  simp only [eqToHom_refl, Category.id_comp]
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro t
  simp only [DegreeLoweringRegrade.regrade_component, eqToHom_refl, Category.id_comp]

theorem congr {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f g : DegreeLoweringHomology.Map C E d) (d' : ℕ) (hd : d' = d) (q : ℕ)
    (h : f.homology q = g.homology q) :
    (DegreeLoweringRegrade.regrade f d' hd).homology q =
      (DegreeLoweringRegrade.regrade g d' hd).homology q := by
  rw [homology, homology, h]

end
end Finsler.DegreeRegradedHomology
