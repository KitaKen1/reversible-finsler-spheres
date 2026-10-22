module

public import Finsler.Topology.NestedCapHomology

/-! Recover the actual nested two-cap degree convention from a closed
degree-lowering operation, preserving boundary and source formulas. -/

@[expose] public section
namespace Finsler.NestedCapUnpack

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

variable {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (a b : ℕ)
  (f : DegreeLoweringHomology.Map C D (a + b))

def component (q : ℕ) : C.X (a + (b + q)) ⟶ D.X q :=
  eqToHom (congrArg C.X (Nat.add_assoc a b q).symm) ≫ f.component q

private theorem transport_d (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i j i' j' : ℕ) (hi : i = i') (hj : j = j') :
    eqToHom (congrArg K.X hi) ≫ K.d i' j' =
      K.d i j ≫ eqToHom (congrArg K.X hj) := by
  subst i'
  subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem comm (q : ℕ) :
    component a b f (q + 1) ≫ D.d (q + 1) q =
      C.d (a + (b + (q + 1))) (a + (b + q)) ≫ component a b f q := by
  have ht := transport_d C (a + (b + (q + 1))) (a + (b + q))
    ((a + b) + (q + 1)) ((a + b) + q)
    (Nat.add_assoc a b (q + 1)).symm (Nat.add_assoc a b q).symm
  dsimp only [component]
  rw [Category.assoc, f.comm, ← Category.assoc, ht, Category.assoc]

theorem inclusion {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (j : D ⟶ E)
    (u : ∀ q, C.X (a + (b + q)) ⟶ E.X q)
    (hu : ∀ q, f.component q ≫ j.f q =
      eqToHom (congrArg C.X (Nat.add_assoc a b q)) ≫ u q) (q : ℕ) :
    component a b f q ≫ j.f q = u q := by
  dsimp only [component]
  rw [Category.assoc, hu q, ← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]

theorem repack_component (q : ℕ) :
    (NestedCapHomology.operation a b (component a b f) (comm a b f)).component q = f.component q := by
  change eqToHom _ ≫ (eqToHom _ ≫ f.component q) = _
  rw [← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]

end
end Finsler.NestedCapUnpack
