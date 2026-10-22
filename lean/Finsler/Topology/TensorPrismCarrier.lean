module

public import Finsler.Topology.SmallCrossCarrier
public import Finsler.Topology.TensorPrismSummands
public import Finsler.Topology.FactorwiseSubdivisionComparison
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! The actual factorwise/product subdivision comparison keeps each pair
of parent simplex images, including every component of its tensor prism. -/

@[expose] public section
namespace Finsler.TensorPrismCarrier

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti
open Finsler.SmallRectangleShuffle Finsler.SmallRectangleCross
open Finsler.TensorApproximationHomotopy Finsler.TensorPrismSummands
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {X Y : TopCat.{0}} {ι κ γ δ : Type*}

theorem cross_preserves_at (W : γ → Set X) (Z : δ → Set Y)
    (p q n : ℕ) (h : p + q = n)
    {c : coeff ⟶ (chains X).X p} {d : coeff ⟶ (chains Y).X q}
    (hc : c ∈ supported X W p) (hd : d ∈ supported Y Z q) :
    (λ_ coeff).inv ≫ (c ⊗ₘ d) ≫ ιTensorObj (chains X) (chains Y) p q n h ≫
      (ambient X Y).f n ∈ supported (X ⊗ Y) (rectangles W Z) n := by
  subst n
  simpa only [SingularChainCross.component, ambient, HomologicalComplex.comp_f, Category.assoc] using
    SmallCrossCarrier.cross_preserves W Z p q hc hd

private theorem units_preserves {A : TopCat.{0}} {ε : Type*} (W : ε → Set A) (n : ℕ)
    (r : ℤˣ) {c : coeff ⟶ (chains A).X n} (hc : c ∈ supported A W n) :
    r • c ∈ supported A W n := by
  change (r : ℤ) • c ∈ supported A W n
  exact (supported A W n).zsmul_mem hc (r : ℤ)

theorem approximation_preserves (U : ι → Set X) (V : κ → Set Y)
    (W : γ → Set X) (Z : δ → Set Y) (p q : ℕ)
    {c : coeff ⟶ (chains X).X p} {d : coeff ⟶ (chains Y).X q}
    (hc : c ∈ supported X W p) (hd : d ∈ supported Y Z q) :
    (λ_ coeff).inv ≫ (c ⊗ₘ d) ≫ ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫
      (approximation U V).hom (p + q) (p + q + 1) ≫ (ambient X Y).f (p + q + 1) ∈
        supported (X ⊗ Y) (rectangles W Z) (p + q + 1) := by
  have ha : (approximation U V).hom (p + q) (p + q + 1) =
      (tensorHomotopy (singularSmallApproxHomotopy coeff U)
        (singularSmallApproxHomotopy coeff V)).hom (p + q) (p + q + 1) := by
    exact (TensorApproximationComponents.approximation_hom U V (p + q) (p + q + 1)).trans
      (TensorApproximationComponents.tensor_hom (singularSmallApproxHomotopy coeff U)
        (singularSmallApproxHomotopy coeff V) (p + q) (p + q + 1)).symm
  have hcH := approximationPrism_preserves U W hc
  have hcA := SmallChainCarrier.approximation_preserves U W hc
  have hdH := approximationPrism_preserves V Z hd
  have ht₁ := cross_preserves_at W Z (p + 1) q (p + q + 1) (by omega) hcH hd
  have ht₂ := cross_preserves_at W Z p (q + 1) (p + q + 1) (by omega) hcA hdH
  have he := congrArg (fun f => (λ_ coeff).inv ≫ (c ⊗ₘ d) ≫ f ≫ (ambient X Y).f (p + q + 1))
    (on_summand (singularSmallApproxHomotopy coeff U) (singularSmallApproxHomotopy coeff V) p q)
  simp only [Category.assoc] at he
  rw [ha, he]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.comp_units_smul,
    Linear.units_smul_comp, Category.assoc, tensorHom_comp_tensorHom_assoc,
    HomologicalComplex.id_f, Category.comp_id]
  exact (supported (X ⊗ Y) (rectangles W Z) (p + q + 1)).add_mem
    (units_preserves _ _ _ ht₁) (units_preserves _ _ _ ht₂)

theorem approximation_parent (U : ι → Set X) (V : κ → Set Y) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    (λ_ coeff).inv ≫ ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
      (TopCat.toSSet.obj Y).ιChainComplex τ) ≫
      ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫
      (approximation U V).hom (p + q) (p + q + 1) ≫ (ambient X Y).f (p + q + 1) ∈
        supported (X ⊗ Y) (rectangles (parentFamily σ) (parentFamily τ)) (p + q + 1) :=
  approximation_preserves U V (parentFamily σ) (parentFamily τ) p q
    (simplex_parent σ) (simplex_parent τ)

variable (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)

theorem comparison_inclusion (n : ℕ) :
    (FactorwiseSubdivisionComparison.comparison U V hU hcoverU hV hcoverV).hom n (n + 1) ≫
        (inclusion (X ⊗ Y) (rectangles U V)).f (n + 1) =
      (approximation U V).hom n (n + 1) ≫ (ambient X Y).f (n + 1) ≫
        (singularSmallApprox coeff (rectangles U V)).f (n + 1) := by
  have hp : (FactorwiseSubdivisionComparison.productRetraction U V hU hcoverU hV hcoverV).f (n + 1) ≫
      (inclusion (X ⊗ Y) (rectangles U V)).f (n + 1) =
        (singularSmallApprox coeff (rectangles U V)).f (n + 1) :=
    congrArg (fun f => f.f (n + 1)) (smallSingularRetraction_comp_ι (X := X ⊗ Y) coeff
      (rectangles U V) (FactorwiseSubdivisionComparison.rectangles_open U V hU hV)
      (FactorwiseSubdivisionComparison.rectangles_cover U V hcoverU hcoverV))
  change (0 + ((approximation U V).hom n (n + 1) ≫
    (ambient X Y ≫ FactorwiseSubdivisionComparison.productRetraction U V hU hcoverU hV hcoverV).f
      (n + 1) + 0)) ≫ _ = _
  simp only [zero_add, add_zero, HomologicalComplex.comp_f, Category.assoc]
  rw [hp]

theorem comparison_preserves (W : γ → Set X) (Z : δ → Set Y) (p q : ℕ)
    {c : coeff ⟶ (chains X).X p} {d : coeff ⟶ (chains Y).X q}
    (hc : c ∈ supported X W p) (hd : d ∈ supported Y Z q) :
    (λ_ coeff).inv ≫ (c ⊗ₘ d) ≫ ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫
      (FactorwiseSubdivisionComparison.comparison U V hU hcoverU hV hcoverV).hom (p + q) (p + q + 1) ≫
      (inclusion (X ⊗ Y) (rectangles U V)).f (p + q + 1) ∈
        supported (X ⊗ Y) (rectangles W Z) (p + q + 1) := by
  rw [comparison_inclusion]
  simp only [← Category.assoc]
  exact SmallChainCarrier.approximation_preserves (rectangles U V) (rectangles W Z)
    (approximation_preserves U V W Z p q hc hd)

theorem comparison_parent (p q : ℕ) (σ : TopCat.toSSet.obj X _⦋p⦌)
    (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    (λ_ coeff).inv ≫ ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
      (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫
      (FactorwiseSubdivisionComparison.comparison U V hU hcoverU hV hcoverV).hom (p + q) (p + q + 1) ≫
      (inclusion (X ⊗ Y) (rectangles U V)).f (p + q + 1) ∈
        supported (X ⊗ Y) (rectangles (parentFamily σ) (parentFamily τ)) (p + q + 1) :=
  comparison_preserves U V hU hcoverU hV hcoverV (parentFamily σ) (parentFamily τ) p q
    (simplex_parent σ) (simplex_parent τ)

end
end Finsler.TensorPrismCarrier
