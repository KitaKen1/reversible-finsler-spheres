module

public import Finsler.Topology.FilteredBilinearLoopProduct
public import TauCeti.Algebra.Homology.Monoidal.KoszulBraiding

/-! Actual tensor cycles and their homology cross commute with the
genuine Koszul chain braiding over F2, including degree zero. -/

@[expose] public section
namespace Finsler.F2TensorHomologySwap
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

variable (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (i j k : ℕ) (h : i + j = k)

theorem cycles : cyclesCross C D i j k h ≫
    cyclesMap (TauCeti.NatChainComplex.koszulBraidingHom C D) k =
    (β_ (C.cycles i) (D.cycles j)).hom ≫ cyclesCross D C j i k (by omega) := by
  apply (cancel_mono ((HomologicalComplex.tensorObj D C).iCycles k)).mp
  simp only [Category.assoc, cyclesMap_i, cyclesCross_iCycles]
  rw [← Category.assoc (cyclesCross C D i j k h), cyclesCross_iCycles,
    Category.assoc, TauCeti.NatChainComplex.ιTensorObj_koszulBraidingHom_f,
    sign_smul, BraidedCategory.braiding_naturality_assoc]

theorem homology : homologyCross C D i j k h ≫
    homologyMap (TauCeti.NatChainComplex.koszulBraidingHom C D) k =
    (β_ (C.homology i) (D.homology j)).hom ≫ homologyCross D C j i k (by omega) := by
  apply homology_tensor_homology_hom_ext C D i j
  simp only [homologyπ_tensorHom_homologyCross_assoc]
  rw [homologyπ_naturality, ← Category.assoc, cycles C D i j k h,
    Category.assoc, BraidedCategory.braiding_naturality_assoc,
    homologyπ_tensorHom_homologyCross]

end
end Finsler.F2TensorHomologySwap
