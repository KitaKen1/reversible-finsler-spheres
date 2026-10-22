module

public import Finsler.Loop.DegreeLoweringComposition

/-! Carry genuine same-target time comparisons and splits through
the first closed join cap, with the exact degree transports retained. -/

@[expose] public section
namespace Finsler.DegreeLoweringCompositionPostHomology

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

theorem post_congr {C D E F : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {a b : ℕ}
    (f : DegreeLoweringHomology.Map C D a) (g : DegreeLoweringHomology.Map D E b)
    (j : E ⟶ F) (k : DegreeLoweringHomology.Map D F b) (q : ℕ)
    (h : (g.post j).homology q = k.homology q) :
    ((DegreeLoweringComposition.compose f g).post j).homology q =
      (DegreeLoweringComposition.compose f k).homology q := by
  rw [DegreeLoweringHomology.Map.post_homology] at h
  simp only [DegreeLoweringHomology.Map.post_homology, DegreeLoweringComposition.homology, Category.assoc]
  rw [h]

theorem split {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {a b : ℕ}
    (f : DegreeLoweringHomology.Map C D a) (g g₁ g₂ : DegreeLoweringHomology.Map D E b) (q : ℕ)
    (h : g.homology q = g₁.homology q + g₂.homology q) :
    (DegreeLoweringComposition.compose f g).homology q =
      (DegreeLoweringComposition.compose f g₁).homology q + (DegreeLoweringComposition.compose f g₂).homology q := by
  simp only [DegreeLoweringComposition.homology, h, Preadditive.comp_add]

end
end Finsler.DegreeLoweringCompositionPostHomology
