module

public import Finsler.Loop.DegreeLoweringComposition
public import Finsler.Loop.LocalizedCapCupComponentSource

/-! Move a genuine ordinary input map through the actual closed
composition, preserving the native associativity transport. -/

@[expose] public section
namespace Finsler.DegreeLoweringCompositionInput
open CategoryTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem pre_homology {K C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {a b : ℕ}
    (j : K ⟶ C) (f : DegreeLoweringHomology.Map C D a) (g : DegreeLoweringHomology.Map D E b) (q : ℕ) :
    (DegreeLoweringComposition.compose (f.pre j) g).homology q =
      ((DegreeLoweringComposition.compose f g).pre j).homology q := by
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro k
  simp only [DegreeLoweringComposition.component, DegreeLoweringHomology.Map.pre, Category.assoc]
  rw [← Category.assoc (eqToHom _) (j.f _), LocalizedCapCupComponentSource.transport_f]
  simp only [Category.assoc]
  omega

theorem middle_homology {C D E F : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {a b : ℕ}
    (f : DegreeLoweringHomology.Map C D a) (j : D ⟶ E) (g : DegreeLoweringHomology.Map E F b) (q : ℕ) :
    (DegreeLoweringComposition.compose (f.post j) g).homology q =
      (DegreeLoweringComposition.compose f (g.pre j)).homology q := by
  simp only [DegreeLoweringComposition.homology, DegreeLoweringHomology.Map.pre_homology,
    DegreeLoweringHomology.Map.post_homology, Category.assoc]

end
end Finsler.DegreeLoweringCompositionInput
