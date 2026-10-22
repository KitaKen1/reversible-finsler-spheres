module

public import Finsler.Topology.TensorApproximationComponents
import all Mathlib.Algebra.Homology.BifunctorHomotopy

/-! Compute the actual tensor prism on each homogeneous summand. Keep
the genuine total-complex signs; they do not change carrier membership. -/

@[expose] public section
namespace Finsler.TensorPrismSummands

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.TensorApproximationHomotopy Finsler.TensorApproximationComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem on_summand {A B C D : ChainComplex (ModuleCat (ZMod 2)) ℕ}
    {f₀ f₁ : A ⟶ B} {g₀ g₁ : C ⟶ D} (H : Homotopy f₀ f₁) (K : Homotopy g₀ g₁)
    (p q : ℕ) :
    ιTensorObj A C p q (p + q) rfl ≫ (tensorHomotopy H K).hom (p + q) (p + q + 1) =
      ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p + 1, q) •
        ((H.hom p (p + 1) ⊗ₘ g₀.f q) ≫ ιTensorObj B D (p + 1) q (p + q + 1) (by omega)) +
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q + 1) •
        ((f₁.f p ⊗ₘ K.hom q (q + 1)) ≫ ιTensorObj B D p (q + 1) (p + q + 1) (by omega)) := by
  rw [tensor_hom, Preadditive.comp_add]
  apply congrArg₂ (fun x y => x + y)
  · have h := mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ H g₀
      (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ)
      (p + 1) p q (p + q) (p + q + 1) rfl (ChainComplex.prev ℕ p)
    rw [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by change (p + 1) + q = p + q + 1; omega)] at h
    simpa only [curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj,
      tensorHom_def, Linear.units_smul_comp, Category.assoc] using h
  · have h := mapBifunctorMapHomotopy.ιMapBifunctor_hom₂ f₁ K
      (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ)
      p (q + 1) q (p + q) (p + q + 1) rfl (ChainComplex.prev ℕ q)
    rw [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by change p + (q + 1) = p + q + 1; omega)] at h
    simpa only [curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj,
      tensorHom_def, Linear.units_smul_comp, Category.assoc] using h

end
end Finsler.TensorPrismSummands
