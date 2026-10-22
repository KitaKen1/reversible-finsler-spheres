module

public import Finsler.Loop.DegreeLoweringComposition
public import Finsler.Loop.DegreeLoweringRegrade

/-! Preserve exact first-cap agreement under real source refinements
when composing the same closed second cap, including degree regrading. -/

@[expose] public section
namespace Finsler.DegreeLoweringRefinedComposition

open CategoryTheory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {B C D S E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {a b : ℕ}
  (r : B ⟶ C) (s : B ⟶ D) (f : DegreeLoweringHomology.Map C S a)
  (g : DegreeLoweringHomology.Map D S a) (c : DegreeLoweringHomology.Map S E b)
  (h : ∀ q, r.f (a + q) ≫ f.component q = s.f (a + q) ≫ g.component q)

include h in
theorem component_eq (q : ℕ) :
    r.f ((a + b) + q) ≫ (DegreeLoweringComposition.compose f c).component q =
    s.f ((a + b) + q) ≫ (DegreeLoweringComposition.compose g c).component q := by
  rw [DegreeLoweringComposition.component, DegreeLoweringComposition.component]
  simp only [← Category.assoc]
  rw [← transport_f r ((a + b) + q) (a + (b + q)) (Nat.add_assoc a b q),
    ← transport_f s ((a + b) + q) (a + (b + q)) (Nat.add_assoc a b q)]
  simp only [Category.assoc]
  rw [← Category.assoc (r.f (a + (b + q))), h]
  simp only [Category.assoc]

include h in
theorem regraded_component_eq (d : ℕ) (hd : d = a + b) (q : ℕ) :
    r.f (d + q) ≫ (DegreeLoweringRegrade.regrade (DegreeLoweringComposition.compose f c) d hd).component q =
    s.f (d + q) ≫ (DegreeLoweringRegrade.regrade (DegreeLoweringComposition.compose g c) d hd).component q := by
  subst d
  simpa only [DegreeLoweringRegrade.regrade, eqToHom_refl, Category.id_comp] using component_eq r s f g c h q

end
end Finsler.DegreeLoweringRefinedComposition
