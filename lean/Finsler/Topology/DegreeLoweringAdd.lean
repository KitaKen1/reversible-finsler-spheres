module

public import Finsler.Topology.DegreeLoweringExact

/-! Add actual degree-lowering chain operations and identify the sum on
homology, including degree zero. -/

@[expose] public section
namespace Finsler.DegreeLoweringAdd

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] {C D : ChainComplex (ModuleCat.{0} R) ℕ} {p : ℕ}

def sum (f g : DegreeLoweringHomology.Map C D p) : DegreeLoweringHomology.Map C D p where
  component q := f.component q + g.component q
  comm q := by
    simp only [Preadditive.add_comp, f.comm, g.comm, Preadditive.comp_add]

theorem sum_cycles (f g : DegreeLoweringHomology.Map C D p) (q : ℕ) :
    (sum f g).cycles q = f.cycles q + g.cycles q := by
  apply (cancel_mono (D.iCycles q)).mp
  rw [Preadditive.add_comp, DegreeLoweringHomology.Map.cycles_i, f.cycles_i, g.cycles_i]
  change C.iCycles (p + q) ≫ (f.component q + g.component q) = _
  rw [Preadditive.comp_add]

theorem sum_homology (f g : DegreeLoweringHomology.Map C D p) (q : ℕ) :
    (sum f g).homology q = f.homology q + g.homology q := by
  apply (cancel_epi (C.homologyπ (p + q))).mp
  rw [Preadditive.comp_add, DegreeLoweringHomology.Map.homologyπ_homology,
    f.homologyπ_homology, g.homologyπ_homology, sum_cycles, Preadditive.add_comp]

theorem homology_eq_sum_of_cycle_boundary (f g h : DegreeLoweringHomology.Map C D p)
    (q : ℕ) (H : C.X (p + q) ⟶ D.X (q + 1))
    (hH : C.iCycles (p + q) ≫ (f.component q - (g.component q + h.component q)) =
      (C.iCycles (p + q) ≫ H) ≫ D.d (q + 1) q) :
    f.homology q = g.homology q + h.homology q := by
  rw [← sum_homology]
  exact DegreeLoweringExact.homology_eq_of_cycle_boundary f (sum g h) q H hH

end
end Finsler.DegreeLoweringAdd
