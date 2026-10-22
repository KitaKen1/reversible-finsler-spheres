module

public import Finsler.Topology.ChainEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross
public import TauCeti.Algebra.Homology.Monoidal.TensorCochain

/-! Actual evaluation of a tensor cochain on a homology cross product.
This is the algebraic calculation needed to evaluate the sphere factor in the
unit proof; no geometric unit or Kunneth decomposition is assumed. -/

@[expose] public section

namespace Finsler.TensorCrossEvaluation

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open Finsler.CochainComparison Finsler.ChainEvaluation TauCeti.ChainComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}

theorem tensor_zero_left (p q m : ℕ) (ψ : D.X q ⟶ coeff) :
    tensorCochain (ρ_ coeff).hom (0 : C.X p ⟶ coeff) ψ m = 0 := by
  let v := tensorCochain (ρ_ coeff).hom (0 : C.X p ⟶ coeff) ψ m
  have he : v = v + v := by
    simpa only [add_zero] using tensorCochain_add_left (ρ_ coeff).hom
      (0 : C.X p ⟶ coeff) (0 : C.X p ⟶ coeff) ψ m
  exact (add_left_cancel ((add_zero v).trans he)).symm

theorem tensor_zero_right (p q m : ℕ) (φ : C.X p ⟶ coeff) :
    tensorCochain (ρ_ coeff).hom φ (0 : D.X q ⟶ coeff) m = 0 := by
  let v := tensorCochain (ρ_ coeff).hom φ (0 : D.X q ⟶ coeff) m
  have he : v = v + v := by
    simpa only [add_zero] using tensorCochain_add_right (ρ_ coeff).hom φ
      (0 : D.X q ⟶ coeff) (0 : D.X q ⟶ coeff) m
  exact (add_left_cancel ((add_zero v).trans he)).symm

theorem tensor_closed (p q : ℕ) (φ : C.X p ⟶ coeff) (ψ : D.X q ⟶ coeff)
    (hφ : C.d (p + 1) p ≫ φ = 0) (hψ : D.d (q + 1) q ≫ ψ = 0) :
    (HomologicalComplex.tensorObj C D).d (p + q + 1) (p + q) ≫ tensorCochain (ρ_ coeff).hom φ ψ (p + q) = 0 := by
  rw [d_comp_tensorCochain, hφ, hψ, tensor_zero_left, tensor_zero_right, smul_zero, add_zero]

theorem cross_evaluation (p q : ℕ) (φ : C.X p ⟶ coeff) (ψ : D.X q ⟶ coeff)
    (hφ : C.d (p + 1) p ≫ φ = 0) (hψ : D.d (q + 1) q ≫ ψ = 0) :
    homologyCross C D p q (p + q) rfl ≫
        evaluation (HomologicalComplex.tensorObj C D) (p + q) (tensorCochain (ρ_ coeff).hom φ ψ (p + q))
          (tensor_closed p q φ ψ hφ hψ) =
      (evaluation C p φ hφ ⊗ₘ evaluation D q ψ hψ) ≫ (ρ_ coeff).hom := by
  refine homology_tensor_homology_hom_ext C D p q ?_
  calc
    _ = (C.iCycles p ⊗ₘ D.iCycles q) ≫ ((φ ⊗ₘ ψ) ≫ (ρ_ coeff).hom) := by
      rw [← Category.assoc, homologyπ_tensorHom_homologyCross, Category.assoc,
        homologyπ_evaluation, ← Category.assoc, cyclesCross_iCycles,
        Category.assoc, ιTensorObj_tensorCochain]
    _ = ((C.iCycles p ≫ φ) ⊗ₘ (D.iCycles q ≫ ψ)) ≫ (ρ_ coeff).hom := by
      rw [tensorHom_comp_tensorHom_assoc]
    _ = ((C.homologyπ p ≫ evaluation C p φ hφ) ⊗ₘ
        (D.homologyπ q ≫ evaluation D q ψ hψ)) ≫ (ρ_ coeff).hom := by
      rw [homologyπ_evaluation, homologyπ_evaluation]
    _ = _ := by rw [tensorHom_comp_tensorHom_assoc]

theorem cross_evaluation_of_ne (p q i j : ℕ) (h : i + j = p + q) (hi : i ≠ p)
    (φ : C.X p ⟶ coeff) (ψ : D.X q ⟶ coeff)
    (hφ : C.d (p + 1) p ≫ φ = 0) (hψ : D.d (q + 1) q ≫ ψ = 0) :
    homologyCross C D i j (p + q) h ≫
      evaluation (HomologicalComplex.tensorObj C D) (p + q) (tensorCochain (ρ_ coeff).hom φ ψ (p + q))
        (tensor_closed p q φ ψ hφ hψ) = 0 := by
  refine homology_tensor_homology_hom_ext C D i j ?_
  rw [← Category.assoc, homologyπ_tensorHom_homologyCross, Category.assoc,
    homologyπ_evaluation, ← Category.assoc, cyclesCross_iCycles, Category.assoc,
    ιTensorObj_tensorCochain_of_ne_left _ _ _ h hi, comp_zero, comp_zero]


end
end Finsler.TensorCrossEvaluation
