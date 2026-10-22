module

public import Finsler.Topology.DegreeLoweringHomology

/-! The actual nested two-cap degree convention yields a genuine
degree-lowering homology operation, including output degree zero. -/

@[expose] public section
namespace Finsler.NestedCapHomology

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def operation {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (k p : ℕ)
    (u : ∀ q, C.X (k + (p + q)) ⟶ D.X q)
    (hu : ∀ q, u (q + 1) ≫ D.d (q + 1) q =
      C.d (k + (p + (q + 1))) (k + (p + q)) ≫ u q) :
    DegreeLoweringHomology.Map C D (k + p) where
  component q := eqToHom (congrArg C.X (Nat.add_assoc k p q)) ≫ u q
  comm q := by
    have ht : eqToHom (congrArg C.X (Nat.add_assoc k p (q + 1))) ≫
        C.d (k + (p + (q + 1))) (k + (p + q)) =
      C.d ((k + p) + (q + 1)) ((k + p) + q) ≫
        eqToHom (congrArg C.X (Nat.add_assoc k p q)) := by
      have H (i j i' j' : ℕ) (hi : i = i') (hj : j = j') :
          eqToHom (congrArg C.X hi) ≫ C.d i' j' = C.d i j ≫ eqToHom (congrArg C.X hj) := by
        subst i'
        subst j'
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact H _ _ _ _ (Nat.add_assoc k p (q + 1)) (Nat.add_assoc k p q)
    rw [Category.assoc, hu q, ← Category.assoc, ht, Category.assoc]

end
end Finsler.NestedCapHomology
