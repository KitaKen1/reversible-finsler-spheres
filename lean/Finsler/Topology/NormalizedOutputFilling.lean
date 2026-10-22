module

public import Finsler.Topology.NormalizationCarrier

/-! A cycle killed by the actual normalization projector has an explicit
filling in the same target space, including degree zero. In particular
the target may itself be the retained-length sublevel; no homology
injectivity of its ambient inclusion is used. -/

@[expose] public section
namespace Finsler.NormalizedOutputFilling

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cycle_boundary (Y : TopCat.{0}) (q : ℕ) (M : ModuleCat.{0} (ZMod 2))
    (c : M ⟶ (chains Y).cycles q)
    (hnorm : c ≫ (chains Y).iCycles q ≫ (SingularNormalization.projector Y).f q = 0) :
    c ≫ (chains Y).iCycles q =
      (-(c ≫ (chains Y).iCycles q ≫
        (SingularNormalization.projectorHomotopy Y).hom q (q + 1))) ≫
          (chains Y).d (q + 1) q := by
  let H := SingularNormalization.projectorHomotopy Y
  have hd : (c ≫ (chains Y).iCycles q) ≫ _root_.dNext q H.hom = 0 := by
    change (c ≫ (chains Y).iCycles q) ≫
      ((chains Y).d q _ ≫ H.hom _ q) = 0
    simp only [Category.assoc, (chains Y).iCycles_d_assoc, zero_comp, comp_zero]
  have h := congrArg (fun f => (c ≫ (chains Y).iCycles q) ≫ f) (H.comm q)
  simp only [Preadditive.comp_add, HomologicalComplex.id_f, Category.comp_id] at h
  rw [hd, Homotopy.prevD_chainComplex, zero_add] at h
  have hz : c ≫ (chains Y).iCycles q ≫ (SingularNormalization.projector Y).f q =
      (c ≫ (chains Y).iCycles q) ≫ (SingularNormalization.projector Y).f q :=
    (Category.assoc _ _ _).symm
  rw [← hz, hnorm] at h
  rw [Preadditive.neg_comp]
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [Category.assoc, add_comm] using h.symm

end
end Finsler.NormalizedOutputFilling
