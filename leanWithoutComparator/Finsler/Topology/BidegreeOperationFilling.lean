module

public import Finsler.Topology.DegreeLoweringHomology
public import Finsler.Topology.NormalizedOutputFilling
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross

/-! Actual cycles and homology classes in a fixed cross-product
bidegree. Normalized zero only on that summand yields an explicit
filling in the same target and zero on its actual homology product.
The entire unlabelled operation need not be zero. -/

@[expose] public section
namespace Finsler.BidegreeOperationFilling

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {K L C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (Y : TopCat.{0})
  (s : K ⊗ L ⟶ C) {m : ℕ} (u : DegreeLoweringHomology.Map C (chains Y) m)
  (j k q : ℕ) (htotal : j + k = m + q)

def cycles : K.cycles j ⊗ L.cycles k ⟶ (chains Y).cycles q :=
  HomologicalComplex.cyclesCross K L j k (m + q) htotal ≫
    HomologicalComplex.cyclesMap s (m + q) ≫ u.cycles q

theorem cycles_i : cycles Y s u j k q htotal ≫ (chains Y).iCycles q =
    (K.iCycles j ⊗ₘ L.iCycles k) ≫ ιTensorObj K L j k (m + q) htotal ≫
      s.f (m + q) ≫ u.component q := by
  have hcross : HomologicalComplex.cyclesCross K L j k (m + q) htotal ≫
      (K ⊗ L).iCycles (m + q) =
      (K.iCycles j ⊗ₘ L.iCycles k) ≫ ιTensorObj K L j k (m + q) htotal :=
    HomologicalComplex.cyclesCross_iCycles K L j k (m + q) htotal
  unfold cycles
  rw [Category.assoc, Category.assoc, u.cycles_i,
    ← Category.assoc (HomologicalComplex.cyclesMap s (m + q)),
    HomologicalComplex.cyclesMap_i]
  simp only [← Category.assoc]
  rw [hcross]

variable (hnorm : ιTensorObj K L j k (m + q) htotal ≫ s.f (m + q) ≫ u.component q ≫
  (SingularNormalization.projector Y).f q = 0)

include hnorm in
theorem cycle_boundary :
    cycles Y s u j k q htotal ≫ (chains Y).iCycles q =
      (-(cycles Y s u j k q htotal ≫ (chains Y).iCycles q ≫
        (SingularNormalization.projectorHomotopy Y).hom q (q + 1))) ≫
          (chains Y).d (q + 1) q := by
  apply NormalizedOutputFilling.cycle_boundary
  rw [← Category.assoc, cycles_i]
  simpa only [Category.assoc, hnorm, comp_zero]

include hnorm in
theorem homology_zero :
    HomologicalComplex.homologyCross K L j k (m + q) htotal ≫
      HomologicalComplex.homologyMap s (m + q) ≫ u.homology q = 0 := by
  let b := -(cycles Y s u j k q htotal ≫ (chains Y).iCycles q ≫
    (SingularNormalization.projectorHomotopy Y).hom q (q + 1))
  have hc : cycles Y s u j k q htotal = b ≫ (chains Y).toCycles (q + 1) q := by
    apply (cancel_mono ((chains Y).iCycles q)).mp
    rw [Category.assoc, (chains Y).toCycles_i]
    exact cycle_boundary Y s u j k q htotal hnorm
  have hz : cycles Y s u j k q htotal ≫ (chains Y).homologyπ q = 0 := by
    rw [hc, Category.assoc, (chains Y).toCycles_comp_homologyπ, comp_zero]
  apply HomologicalComplex.homology_tensor_homology_hom_ext K L j k
  rw [← Category.assoc, HomologicalComplex.homologyπ_tensorHom_homologyCross,
    Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    u.homologyπ_homology]
  simpa only [cycles, Category.assoc, comp_zero] using hz

end
end Finsler.BidegreeOperationFilling
