module

public import Finsler.Topology.DegreeLoweringHomology

/-! Explicit transport of a genuine closed operation to an equal
degree convention, with the actual component transport formula. -/

@[expose] public section
namespace Finsler.DegreeLoweringRegrade

open CategoryTheory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

private theorem transport_d (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i i' j j' : ℕ) (hi : i = i') (hj : j = j') :
    eqToHom (congrArg C.X hi) ≫ C.d i' j' = C.d i j ≫ eqToHom (congrArg C.X hj) := by
  subst i'
  subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def regrade {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f : DegreeLoweringHomology.Map C E d) (d' : ℕ) (hd : d' = d) :
    DegreeLoweringHomology.Map C E d' where
  component q := eqToHom (congrArg C.X (congrArg (fun k => k + q) hd)) ≫ f.component q
  comm q := by
    rw [Category.assoc, f.comm, ← Category.assoc,
      transport_d C (d' + (q + 1)) (d + (q + 1)) (d' + q) (d + q)
        (congrArg (fun k => k + (q + 1)) hd) (congrArg (fun k => k + q) hd), Category.assoc]

theorem regrade_component {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f : DegreeLoweringHomology.Map C E d) (d' : ℕ) (hd : d' = d) (q : ℕ) :
    (regrade f d' hd).component q =
      eqToHom (congrArg C.X (congrArg (fun k => k + q) hd)) ≫ f.component q := rfl

theorem component_transport {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f : DegreeLoweringHomology.Map C E d) (i j : ℕ) (h : i = j) :
    f.component i ≫ eqToHom (congrArg E.X h) =
      eqToHom (congrArg C.X (congrArg (fun k => d + k) h)) ≫ f.component j := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end
end Finsler.DegreeLoweringRegrade
