module

public import Finsler.Loop.SelfHomotopySweepNaturality

/-! An EXPLICIT degree-two boundary comparison identifies actual
degree-one self-sweeps on homology, even when their endpoint maps
differ. No abstract equality of operations is assumed. -/
@[expose] public section
namespace Finsler.SelfSweepExact
open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {f g : C ⟶ D}
  (H : _root_.Homotopy f f) (K : _root_.Homotopy g g) (q : ℕ)
  (L : C.X q ⟶ D.X (q + 2))
  (h : C.iCycles q ≫ (H.hom q (q + 1) - K.hom q (q + 1)) =
    (C.iCycles q ≫ L) ≫ D.d (q + 2) (q + 1))

include h in
theorem cycles_sub :
    SelfHomotopySweep.cycles H q - SelfHomotopySweep.cycles K q =
      (C.iCycles q ≫ L) ≫ D.toCycles (q + 2) (q + 1) := by
  apply (cancel_mono (D.iCycles (q + 1))).mp
  rw [Preadditive.sub_comp, SelfHomotopySweep.cycles_i, SelfHomotopySweep.cycles_i,
    Category.assoc, D.toCycles_i]
  exact (Preadditive.comp_sub _ _ _).symm.trans h

include h in
theorem homology_eq : SelfHomotopySweep.homology H q = SelfHomotopySweep.homology K q := by
  apply (cancel_epi (C.homologyπ q)).mp
  rw [SelfHomotopySweep.homologyπ_homology, SelfHomotopySweep.homologyπ_homology]
  apply sub_eq_zero.mp
  rw [← Preadditive.sub_comp, cycles_sub H K q L h, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

end
end Finsler.SelfSweepExact
