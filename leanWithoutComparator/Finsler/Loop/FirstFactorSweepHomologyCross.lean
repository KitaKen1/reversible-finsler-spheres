module

public import Finsler.Loop.FirstFactorTensorPrismNaturality
public import Finsler.Loop.SelfHomotopySweep
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross

/-! A genuine FIRST-factor self-sweep takes the ACTUAL homology
cross to the cross of its swept class. The real tensor-homotopy
summand, total-complex signONE and actual cycle quotients prove it. -/
@[expose] public section
namespace Finsler.FirstFactorSweepHomologyCross
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex TauCeti.ChainComplex
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {A B : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {f : A ⟶ B}
  (H : _root_.Homotopy f f) (D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)

abbrev prism := FirstFactorTensorPrismNaturality.prism H D

theorem on_summand (i j : ℕ) :
    ιTensorObj A D i j (i + j) rfl ≫ (prism H D).hom (i + j) (i + j + 1) =
      (H.hom i (i + 1) ⊗ₘ 𝟙 (D.X j)) ≫ ιTensorObj B D (i + 1) j (i + j + 1) (by omega) := by
  simpa only [ComplexShape.ε₁_def, one_smul] using FirstFactorTensorPrismNaturality.on_summand H D i j

theorem cycles (i j : ℕ) :
    cyclesCross A D i j (i + j) rfl ≫ SelfHomotopySweep.cycles (prism H D) (i + j) =
      (SelfHomotopySweep.cycles H i ⊗ₘ 𝟙 (D.cycles j)) ≫
        cyclesCross B D (i + 1) j (i + j + 1) (by omega) := by
  apply (cancel_mono ((B ⊗ D).iCycles (i + j + 1))).mp
  have hiA : cyclesCross A D i j (i + j) rfl ≫ (A ⊗ D).iCycles (i + j) =
      (A.iCycles i ⊗ₘ D.iCycles j) ≫ ιTensorObj A D i j (i + j) rfl := cyclesCross_iCycles A D i j (i + j) rfl
  have hiB : cyclesCross B D (i + 1) j (i + j + 1) (by omega) ≫ (B ⊗ D).iCycles (i + j + 1) =
      (B.iCycles (i + 1) ⊗ₘ D.iCycles j) ≫ ιTensorObj B D (i + 1) j (i + j + 1) (by omega) :=
    cyclesCross_iCycles B D (i + 1) j (i + j + 1) (by omega)
  rw [Category.assoc, SelfHomotopySweep.cycles_i, ← Category.assoc, hiA, Category.assoc]
  dsimp only [SelfHomotopySweep.component]
  rw [on_summand]
  rw [Category.assoc, hiB]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id, SelfHomotopySweep.cycles_i, SelfHomotopySweep.component]

theorem homology (i j : ℕ) :
    homologyCross A D i j (i + j) rfl ≫ SelfHomotopySweep.homology (prism H D) (i + j) =
      (SelfHomotopySweep.homology H i ⊗ₘ 𝟙 (D.homology j)) ≫
        homologyCross B D (i + 1) j (i + j + 1) (by omega) := by
  refine homology_tensor_homology_hom_ext A D i j ?_
  calc
    _ = (cyclesCross A D i j (i + j) rfl ≫ SelfHomotopySweep.cycles (prism H D) (i + j)) ≫
        (B ⊗ D).homologyπ (i + j + 1) := by
      rw [← Category.assoc, homologyπ_tensorHom_homologyCross, Category.assoc,
        SelfHomotopySweep.homologyπ_homology, ← Category.assoc]
    _ = ((SelfHomotopySweep.cycles H i ≫ B.homologyπ (i + 1)) ⊗ₘ D.homologyπ j) ≫
        homologyCross B D (i + 1) j (i + j + 1) (by omega) := by
      have hπ : cyclesCross B D (i + 1) j (i + j + 1) (by omega) ≫ (B ⊗ D).homologyπ (i + j + 1) =
          (B.homologyπ (i + 1) ⊗ₘ D.homologyπ j) ≫ homologyCross B D (i + 1) j (i + j + 1) (by omega) :=
        (homologyπ_tensorHom_homologyCross B D (i + 1) j (i + j + 1) (by omega)).symm
      rw [cycles, Category.assoc, hπ,
        ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = _ := by
      rw [← SelfHomotopySweep.homologyπ_homology]
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

end
end Finsler.FirstFactorSweepHomologyCross
