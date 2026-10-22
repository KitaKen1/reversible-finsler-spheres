module

public import Finsler.Topology.SmallChainCarrier

/-! Actual chain inclusion induced by a refinement of singular covers. -/

@[expose] public section
namespace Finsler.SmallCoverRefinement

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) {ι κ : Type*} (W : ι → Set X) (V : κ → Set X)
  (h : ∀ i, ∃ j, W i ⊆ V j)

include h

theorem subcomplex_le : X.smallSingularSubcomplex W ≤ X.smallSingularSubcomplex V := by
  intro N σ hσ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X W σ).mp hσ
  obtain ⟨j, hj⟩ := h i
  exact (TopCat.mem_smallSingularSubcomplex_iff X V σ).mpr ⟨j, hi.trans hj⟩

def map : small X W ⟶ small X V :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (subcomplex_le X W V h)) coeff

theorem map_inclusion : map X W V h ≫ inclusion X V = inclusion X W := by
  unfold map inclusion
  rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]

end
end Finsler.SmallCoverRefinement
