module

public import Finsler.Topology.TensorPrismSummands

/-! Naturality of the genuine identity-in-first-factor tensor prism.
The actual total-complex signs and component maps are retained. -/

@[expose] public section
namespace Finsler.TensorIdentityPrismNaturality

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.TensorApproximationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

def prism (A : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    {B D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {g₀ g₁ : B ⟶ D} (H : Homotopy g₀ g₁) :=
  tensorHomotopy (Homotopy.refl (𝟙 A)) H

theorem on_summand (A : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    {B D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {g₀ g₁ : B ⟶ D} (H : Homotopy g₀ g₁) (j k : ℕ) :
    ιTensorObj A B j k (j + k) rfl ≫ (prism A H).hom (j + k) (j + k + 1) =
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, k + 1) •
      ((𝟙 (A.X j) ⊗ₘ H.hom k (k + 1)) ≫ ιTensorObj A D j (k + 1) (j + k + 1) (by omega)) := by
  rw [prism, TensorPrismSummands.on_summand]
  simp only [Homotopy.refl, Homotopy.ofEq_hom, Pi.zero_apply, HomologicalComplex.id_f,
    MonoidalPreadditive.zero_tensor, zero_comp, smul_zero, zero_add]

theorem naturality {A A' B B' D D' : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {g₀ g₁ : B ⟶ D} {g₀' g₁' : B' ⟶ D'}
    (H : Homotopy g₀ g₁) (H' : Homotopy g₀' g₁') (f : A ⟶ A') (u : B ⟶ B') (v : D ⟶ D')
    (hh : ∀ k, u.f k ≫ H'.hom k (k + 1) = H.hom k (k + 1) ≫ v.f (k + 1)) (N : ℕ) :
    (f ⊗ₘ u).f N ≫ (prism A' H').hom N (N + 1) =
      (prism A H).hom N (N + 1) ≫ (f ⊗ₘ v).f (N + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro j k htotal
  subst N
  change ιTensorObj A B j k (j + k) rfl ≫
    ((f ⊗ₘ u).f (j + k) ≫ (prism A' H').hom (j + k) (j + k + 1)) =
    ιTensorObj A B j k (j + k) rfl ≫
      ((prism A H).hom (j + k) (j + k + 1) ≫ (f ⊗ₘ v).f (j + k + 1))
  have hi : ιTensorObj A B j k (j + k) rfl ≫ (f ⊗ₘ u).f (j + k) =
      (f.f j ⊗ₘ u.f k) ≫ ιTensorObj A' B' j k (j + k) rfl :=
    HomologicalComplex.ι_tensorHom f u j k (j + k) rfl
  have ho : ιTensorObj A D j (k + 1) (j + k + 1) (by omega) ≫ (f ⊗ₘ v).f (j + k + 1) =
      (f.f j ⊗ₘ v.f (k + 1)) ≫ ιTensorObj A' D' j (k + 1) (j + k + 1) (by omega) :=
    HomologicalComplex.ι_tensorHom f v j (k + 1) (j + k + 1) (by omega)
  rw [← Category.assoc, hi, Category.assoc, on_summand]
  rw [← Category.assoc (ιTensorObj A B j k (j + k) rfl)
    ((prism A H).hom (j + k) (j + k + 1)), on_summand]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
  rw [ho]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, hh]

end
end Finsler.TensorIdentityPrismNaturality
