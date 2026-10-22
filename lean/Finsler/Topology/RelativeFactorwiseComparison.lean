module

public import Finsler.Topology.FactorwiseSubdivisionComparison
public import Finsler.Topology.TensorPrismSummands
public import Finsler.Topology.TimeCylinderComparison
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! The actual tensor subdivision homotopy is zero on the tensor of
already-small chains. A time prism with endpoints in those common small
chains therefore has no input-boundary correction after a closed cap.
The time-prism chain itself is not assumed to be a cycle. -/

@[expose] public section
namespace Finsler.RelativeFactorwiseComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti
open Finsler.TensorApproximationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)

theorem approximation_small_zero (n : ℕ) :
    (inclusion X U ⊗ₘ inclusion Y V).f n ≫ (approximation U V).hom n (n + 1) = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  subst n
  simp only [comp_zero]
  change ιTensorObj (small X U) (small Y V) p q (p + q) rfl ≫
    ((inclusion X U ⊗ₘ inclusion Y V).f (p + q) ≫
      (approximation U V).hom (p + q) (p + q + 1)) = 0
  have hi : ιTensorObj (small X U) (small Y V) p q (p + q) rfl ≫
      (inclusion X U ⊗ₘ inclusion Y V).f (p + q) =
      ((inclusion X U).f p ⊗ₘ (inclusion Y V).f q) ≫
        ιTensorObj (chains X) (chains Y) p q (p + q) rfl :=
    HomologicalComplex.ι_tensorHom (inclusion X U) (inclusion Y V) p q (p + q) rfl
  have ha : (approximation U V).hom (p + q) (p + q + 1) =
      (tensorHomotopy (singularSmallApproxHomotopy coeff U)
        (singularSmallApproxHomotopy coeff V)).hom (p + q) (p + q + 1) :=
    (Finsler.TensorApproximationComponents.approximation_hom U V (p + q) (p + q + 1)).trans
      (Finsler.TensorApproximationComponents.tensor_hom (singularSmallApproxHomotopy coeff U)
        (singularSmallApproxHomotopy coeff V) (p + q) (p + q + 1)).symm
  have hx : (inclusion X U).f p ≫ (singularSmallApproxHomotopy coeff U).hom p (p + 1) = 0 :=
    ι_comp_singularSmallApproxHom coeff U p (p + 1)
  have hy : (inclusion Y V).f q ≫ (singularSmallApproxHomotopy coeff V).hom q (q + 1) = 0 :=
    ι_comp_singularSmallApproxHom coeff V q (q + 1)
  rw [← Category.assoc, hi, Category.assoc, ha, Finsler.TensorPrismSummands.on_summand]
  simp only [Preadditive.comp_add, Linear.comp_units_smul, Category.assoc,
    tensorHom_comp_tensorHom_assoc, hx, hy, MonoidalPreadditive.zero_tensor,
    MonoidalPreadditive.tensor_zero, zero_comp, smul_zero, add_zero, comp_zero]

variable (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ k, IsOpen (V k)) (hcV : ⋃ k, V k = Set.univ)

theorem comparison_small_zero (n : ℕ) :
    (inclusion X U ⊗ₘ inclusion Y V).f n ≫
      (FactorwiseSubdivisionComparison.comparison U V hU hcU hV hcV).hom n (n + 1) = 0 := by
  simp only [FactorwiseSubdivisionComparison.comparison, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compRight_hom, Pi.zero_apply, zero_add, add_zero]
  rw [← Category.assoc, approximation_small_zero, zero_comp]

theorem prism_boundary {A E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {a₀ a₁ : A ⟶ chains X ⊗ chains Y} (H : Homotopy a₀ a₁)
    (e₀ e₁ : A ⟶ small X U ⊗ small Y V)
    (he₀ : a₀ = e₀ ≫ (inclusion X U ⊗ₘ inclusion Y V))
    (he₁ : a₁ = e₁ ≫ (inclusion X U ⊗ₘ inclusion Y V))
    (d : ℕ) (u : ∀ q,
      (small (X ⊗ Y) (SmallRectangleShuffle.rectangles U V)).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small (X ⊗ Y) (SmallRectangleShuffle.rectangles U V)).d (d + q + 2) (d + q + 1) ≫ u q)
    (q : ℕ) :
    (A.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1)) ≫
      (((SmallRectangleCross.ambient X Y ≫
          FactorwiseSubdivisionComparison.productRetraction U V hU hcU hV hcV).f (d + q + 1) -
        (FactorwiseSubdivisionComparison.factorwise U V hU hcU hV hcV).f (d + q + 1)) ≫ u q) =
    (A.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1) ≫
      (FactorwiseSubdivisionComparison.comparison U V hU hcU hV hcV).hom (d + q + 1) (d + q + 2) ≫
        u (q + 1)) ≫ E.d (q + 1) q := by
  have hz₀ (q : ℕ) : a₀.f (d + q) ≫
      ((FactorwiseSubdivisionComparison.comparison U V hU hcU hV hcV).hom (d + q) (d + q + 1) ≫ u q) = 0 := by
    rw [he₀, HomologicalComplex.comp_f, Category.assoc]
    rw [← Category.assoc ((inclusion X U ⊗ₘ inclusion Y V).f (d + q)), comparison_small_zero,
      zero_comp, comp_zero]
  have hz₁ (q : ℕ) : a₁.f (d + q) ≫
      ((FactorwiseSubdivisionComparison.comparison U V hU hcU hV hcV).hom (d + q) (d + q + 1) ≫ u q) = 0 := by
    rw [he₁, HomologicalComplex.comp_f, Category.assoc]
    rw [← Category.assoc ((inclusion X U ⊗ₘ inclusion Y V).f (d + q)), comparison_small_zero,
      zero_comp, comp_zero]
  simpa only [Category.assoc] using TimeCylinderComparison.cycle_boundary H
    (FactorwiseSubdivisionComparison.comparison U V hU hcU hV hcV) d u hu hz₀ hz₁ q

end
end Finsler.RelativeFactorwiseComparison
