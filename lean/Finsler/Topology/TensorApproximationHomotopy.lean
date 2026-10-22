module

public import Finsler.Topology.SmallChainCarrier
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import TauCeti.Algebra.Homology.Monoidal.Summand

/-! Tensor the two actual subdivision homotopies, with the total-complex
sign rule supplied by the pinned mathlib bifunctor homotopy construction. -/

@[expose] public section
namespace Finsler.TensorApproximationHomotopy

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def tensorHomotopy {A B C D : ChainComplex (ModuleCat (ZMod 2)) ℕ}
    {f₀ f₁ : A ⟶ B} {g₀ g₁ : C ⟶ D} (H : Homotopy f₀ f₁) (K : Homotopy g₀ g₁) :
    Homotopy (f₀ ⊗ₘ g₀) (f₁ ⊗ₘ g₁) := by
  have h₁ := mapBifunctorMapHomotopy₁ H g₀ (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ)
  have h₂ := mapBifunctorMapHomotopy₂ f₁ K (curriedTensor (ModuleCat (ZMod 2))) (ComplexShape.down ℕ)
  simpa only [← tensorHom_eq_mapBifunctorMap] using h₁.trans h₂

def approximation {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y) :
    Homotopy (𝟙 (chains X ⊗ chains Y))
      (singularSmallApprox coeff U ⊗ₘ singularSmallApprox coeff V) :=
  (Homotopy.ofEq (id_tensorHom_id (chains X) (chains Y)).symm).trans
    (tensorHomotopy (singularSmallApproxHomotopy coeff U) (singularSmallApproxHomotopy coeff V))

end
end Finsler.TensorApproximationHomotopy
