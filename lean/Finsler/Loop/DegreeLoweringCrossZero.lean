module

public import Finsler.Loop.DegreeLoweringCrossSummand

/-! A genuine closed degree-lowering operation vanishes on homology
cross inputs whenever its actual native chain summand is literally
zero. No assertion about all tensor homology is needed. -/

@[expose] public section
namespace Finsler.DegreeLoweringCrossZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {R : Type} [CommRing R]
  (C K E : ChainComplex (ModuleCat.{0} R) ℕ) (d : ℕ)
  (f : DegreeLoweringHomology.Map (HomologicalComplex.tensorObj C K) E d)
  (i j k : ℕ) (hij : i + j = d + k)
  (hs : ιTensorObj C K i j (d + k) hij ≫ f.component k = 0)

include hs in
theorem cycles : cyclesCross C K i j (d + k) hij ≫ f.cycles k = 0 := by
  apply (cancel_mono (E.iCycles k)).mp
  rw [Category.assoc, DegreeLoweringHomology.Map.cycles_i,
    ← Category.assoc (cyclesCross C K i j (d + k) hij), cyclesCross_iCycles,
    Category.assoc, hs, comp_zero, zero_comp]

include hs in
theorem homology : homologyCross C K i j (d + k) hij ≫ f.homology k = 0 := by
  apply homology_tensor_homology_hom_ext C K i j
  rw [homologyπ_tensorHom_homologyCross_assoc, DegreeLoweringHomology.Map.homologyπ_homology,
    ← Category.assoc, cycles C K E d f i j k hij hs, zero_comp, comp_zero]

end
end Finsler.DegreeLoweringCrossZero
