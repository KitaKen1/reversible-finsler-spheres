module

public import Finsler.Topology.TensorPrismSummands
public import Finsler.Topology.SimplicialChainCross

/-! Naturality of a genuine first-factor prism tensor an identity.
No symmetry of the shuffle or reordering of tensor inputs is used. -/

@[expose] public section
namespace Finsler.FirstFactorTensorPrismNaturality

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.TensorApproximationHomotopy Finsler.CochainComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

def prism {A B : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : A ⟶ B} (H : Homotopy f₀ f₁)
    (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :=
  tensorHomotopy H (Homotopy.refl (𝟙 C))

theorem on_summand {A B : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : A ⟶ B} (H : Homotopy f₀ f₁)
    (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j k : ℕ) :
    ιTensorObj A C j k (j + k) rfl ≫ (prism H C).hom (j + k) (j + k + 1) =
    ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j + 1, k) •
      ((H.hom j (j + 1) ⊗ₘ 𝟙 (C.X k)) ≫ ιTensorObj B C (j + 1) k (j + k + 1) (by omega)) := by
  rw [prism, TensorPrismSummands.on_summand]
  simp only [Homotopy.refl, Homotopy.ofEq_hom, Pi.zero_apply, HomologicalComplex.id_f,
    MonoidalPreadditive.tensor_zero, zero_comp, smul_zero, add_zero]

theorem naturality {A A' B B' C C' : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : A ⟶ B} {f₀' f₁' : A' ⟶ B'}
    (H : Homotopy f₀ f₁) (H' : Homotopy f₀' f₁') (u : A ⟶ A') (v : B ⟶ B') (g : C ⟶ C')
    (hh : ∀ j, u.f j ≫ H'.hom j (j + 1) = H.hom j (j + 1) ≫ v.f (j + 1)) (N : ℕ) :
    (u ⊗ₘ g).f N ≫ (prism H' C').hom N (N + 1) =
      (prism H C).hom N (N + 1) ≫ (v ⊗ₘ g).f (N + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro j k htotal
  subst N
  change ιTensorObj A C j k (j + k) rfl ≫
    ((u ⊗ₘ g).f (j + k) ≫ (prism H' C').hom (j + k) (j + k + 1)) =
    ιTensorObj A C j k (j + k) rfl ≫
      ((prism H C).hom (j + k) (j + k + 1) ≫ (v ⊗ₘ g).f (j + k + 1))
  have hi : ιTensorObj A C j k (j + k) rfl ≫ (u ⊗ₘ g).f (j + k) =
      (u.f j ⊗ₘ g.f k) ≫ ιTensorObj A' C' j k (j + k) rfl :=
    HomologicalComplex.ι_tensorHom u g j k (j + k) rfl
  have ho : ιTensorObj B C (j + 1) k (j + k + 1) (by omega) ≫ (v ⊗ₘ g).f (j + k + 1) =
      (v.f (j + 1) ⊗ₘ g.f k) ≫ ιTensorObj B' C' (j + 1) k (j + k + 1) (by omega) :=
    HomologicalComplex.ι_tensorHom v g (j + 1) k (j + k + 1) (by omega)
  rw [← Category.assoc, hi, Category.assoc, on_summand]
  rw [← Category.assoc (ιTensorObj A C j k (j + k) rfl)
    ((prism H C).hom (j + k) (j + k + 1)), on_summand]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
  rw [ho]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, hh]

theorem cross_identity_right {K K' L : SSet.{0}} (f : K ⟶ K') :
    (SSet.chainComplexMap f coeff ⊗ₘ 𝟙 (L.chainComplex coeff)) ≫ SimplicialChainCross.cross K' L =
      SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (f ⊗ₘ 𝟙 L) coeff := by
  have hi : SSet.chainComplexMap (𝟙 L) coeff = 𝟙 (L.chainComplex coeff) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map (𝟙 L) = _
    rw [CategoryTheory.Functor.map_id]
  simpa only [hi] using SimplicialChainCross.naturality f (𝟙 L)

end
end Finsler.FirstFactorTensorPrismNaturality

