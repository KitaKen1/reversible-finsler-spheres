module

public import Finsler.Topology.SingularNormalization
public import Finsler.Topology.DegreeLoweringHomology

/-! Zero after actual target normalization implies zero on homology in
that same target, for a genuine closed degree-lowering operation. Output
degree zero is included. The target may itself be a length sublevel. -/

@[expose] public section
namespace Finsler.NormalizedOperationHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem zero_of_component (Y : TopCat.{0}) {C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {p : ℕ}
    (f : DegreeLoweringHomology.Map C (chains Y) p) (q : ℕ)
    (h : f.component q ≫ (SingularNormalization.projector Y).f q = 0) : f.homology q = 0 := by
  have hP : HomologicalComplex.homologyMap (SingularNormalization.projector Y) q =
      𝟙 ((chains Y).homology q) := by
    simpa only [HomologicalComplex.homologyMap_id] using
      (SingularNormalization.projectorHomotopy Y).homologyMap_eq q
  have hc : (f.post (SingularNormalization.projector Y)).cycles q = 0 := by
    apply (cancel_mono ((chains Y).iCycles q)).mp
    rw [DegreeLoweringHomology.Map.cycles_i, zero_comp]
    change C.iCycles (p + q) ≫ (f.component q ≫ (SingularNormalization.projector Y).f q) = 0
    rw [h, comp_zero]
  have hh : (f.post (SingularNormalization.projector Y)).homology q = 0 := by
    apply (cancel_epi (C.homologyπ (p + q))).mp
    rw [DegreeLoweringHomology.Map.homologyπ_homology, hc, zero_comp, comp_zero]
  rw [DegreeLoweringHomology.Map.post_homology, hP, Category.comp_id] at hh
  exact hh

end
end Finsler.NormalizedOperationHomology
