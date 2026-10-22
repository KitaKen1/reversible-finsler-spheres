module

public import Finsler.Topology.DegreeLoweringExact

/-! A comparison boundary defined on genuine cycles already suffices
for homology equality. No arbitrary extension to all chains is needed. -/

@[expose] public section
namespace Finsler.CyclesBoundaryHomology

open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem homology_eq {R : Type} [Ring R]
    {C D : ChainComplex (ModuleCat.{0} R) ℕ} {p : ℕ}
    (f g : DegreeLoweringHomology.Map C D p) (q : ℕ)
    (W : C.cycles (p + q) ⟶ D.X (q + 1))
    (h : C.iCycles (p + q) ≫ (f.component q - g.component q) = W ≫ D.d (q + 1) q) :
    f.homology q = g.homology q := by
  have hc : f.cycles q - g.cycles q = W ≫ D.toCycles (q + 1) q := by
    apply (cancel_mono (D.iCycles q)).mp
    rw [Preadditive.sub_comp, f.cycles_i, g.cycles_i, Category.assoc, D.toCycles_i]
    simpa only [Preadditive.comp_sub] using h
  apply (cancel_epi (C.homologyπ (p + q))).mp
  rw [f.homologyπ_homology, g.homologyπ_homology]
  apply sub_eq_zero.mp
  rw [← Preadditive.sub_comp, hc, Category.assoc, D.toCycles_comp_homologyπ, comp_zero]

end
end Finsler.CyclesBoundaryHomology
