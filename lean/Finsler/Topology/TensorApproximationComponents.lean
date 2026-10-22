module

public import Finsler.Topology.TensorApproximationHomotopy
import all Mathlib.Algebra.Homology.BifunctorHomotopy

/-! Expose the two actual tensor-prism terms of the constructed homotopy.
This fixes its components for the subsequent rectangle-carrier estimates. -/

@[expose] public section
namespace Finsler.TensorApproximationComponents

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti
open Finsler.TensorApproximationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

theorem tensor_hom {A B C D : ChainComplex (ModuleCat (ZMod 2)) ℕ}
    {f₀ f₁ : A ⟶ B} {g₀ g₁ : C ⟶ D} (H : Homotopy f₀ f₁) (K : Homotopy g₀ g₁)
    (i j : ℕ) :
    (tensorHomotopy H K).hom i j =
      mapBifunctorMapHomotopy.hom₁ H g₀ (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ) i j +
      mapBifunctorMapHomotopy.hom₂ f₁ K (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ) i j := rfl

theorem approximation_hom {X Y : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set Y) (i j : ℕ) :
    (approximation U V).hom i j =
      mapBifunctorMapHomotopy.hom₁ (singularSmallApproxHomotopy coeff U) (𝟙 (chains Y))
        (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ) i j +
      mapBifunctorMapHomotopy.hom₂ (singularSmallApprox coeff U) (singularSmallApproxHomotopy coeff V)
        (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ) i j := by
  change 0 + (tensorHomotopy (singularSmallApproxHomotopy coeff U)
    (singularSmallApproxHomotopy coeff V)).hom i j = _
  rw [zero_add, tensor_hom]

end
end Finsler.TensorApproximationComponents
