module

public import Finsler.Loop.SelfHomotopySweep
public import Finsler.Topology.TimePrismNaturality

/-! Naturality of the genuine degree+1 self-homotopy map, before
and after the actual cycle/homology quotients. -/
@[expose] public section
namespace Finsler.SelfHomotopySweepNaturality
open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {C D C' D' : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
  {f : C ⟶ D} {g : C' ⟶ D'} (H : _root_.Homotopy f f) (K : _root_.Homotopy g g)
  (a : C ⟶ C') (b : D ⟶ D')
  (h : ∀ q, a.f q ≫ K.hom q (q + 1) = H.hom q (q + 1) ≫ b.f (q + 1))

include h in
theorem cycles (q : ℕ) :
    HomologicalComplex.cyclesMap a q ≫ SelfHomotopySweep.cycles K q =
      SelfHomotopySweep.cycles H q ≫ HomologicalComplex.cyclesMap b (q + 1) := by
  apply (cancel_mono (D'.iCycles (q + 1))).mp
  calc
    _ = C.iCycles q ≫ (a.f q ≫ K.hom q (q + 1)) := by
      rw [Category.assoc, SelfHomotopySweep.cycles_i, ← Category.assoc,
        HomologicalComplex.cyclesMap_i, Category.assoc]
      rfl
    _ = C.iCycles q ≫ (H.hom q (q + 1) ≫ b.f (q + 1)) :=
      congrArg (fun v => C.iCycles q ≫ v) (h q)
    _ = _ := by
      rw [Category.assoc, HomologicalComplex.cyclesMap_i]
      simpa only [Category.assoc, SelfHomotopySweep.component] using congrArg
        (fun v => v ≫ b.f (q + 1)) (SelfHomotopySweep.cycles_i H q).symm

include h in
theorem homology (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫ SelfHomotopySweep.homology K q =
      SelfHomotopySweep.homology H q ≫ HomologicalComplex.homologyMap b (q + 1) := by
  apply (cancel_epi (C.homologyπ q)).mp
  calc
    _ = (HomologicalComplex.cyclesMap a q ≫ SelfHomotopySweep.cycles K q) ≫ D'.homologyπ (q + 1) := by
      rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
        SelfHomotopySweep.homologyπ_homology, ← Category.assoc]
    _ = (SelfHomotopySweep.cycles H q ≫ HomologicalComplex.cyclesMap b (q + 1)) ≫ D'.homologyπ (q + 1) :=
      congrArg (fun v => v ≫ D'.homologyπ (q + 1)) (cycles H K a b h q)
    _ = _ := by
      rw [Category.assoc, ← HomologicalComplex.homologyπ_naturality]
      simpa only [Category.assoc] using congrArg
        (fun v => v ≫ HomologicalComplex.homologyMap b (q + 1))
        (SelfHomotopySweep.homologyπ_homology H q).symm

end
end Finsler.SelfHomotopySweepNaturality
