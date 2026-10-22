module

public import Finsler.Loop.FirstFactorTensorPrismNaturality
public import Finsler.Topology.SimplicialTimeModelComparison
import all Finsler.Topology.SimplicialTimeModelComparison

/-! Compare product time with time in the first tensor input. Reorder
only the output coordinates into the existing three-factor model, so
the constructive degree-two filling applies without shuffle symmetry. -/

@[expose] public section
namespace Finsler.FirstFactorSimplicialTimeModelComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SSet
open Finsler.CochainComparison Finsler.TripleTimeModelExtension Finsler.SimplicialTimeCylinder
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

def reorder (K L : SSet.{0}) : ((Δ[1] : SSet.{0}) ⊗ K) ⊗ L ⟶ target K L :=
  ((β_ (Δ[1] : SSet.{0}) K).hom ▷ L) ≫ (α_ K (Δ[1] : SSet.{0}) L).hom

theorem reorder_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    ((𝟙 (Δ[1] : SSet.{0}) ⊗ₘ f) ⊗ₘ g) ≫ reorder K' L' =
      reorder K L ≫ (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

theorem zero_reorder (K L : SSet.{0}) :
    ((SSet.ι₀ ≫ swap K) ⊗ₘ 𝟙 L) ≫ reorder K L = face₀ K L := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

theorem one_reorder (K L : SSet.{0}) :
    ((SSet.ι₁ ≫ swap K) ⊗ₘ 𝟙 L) ≫ reorder K L = face₁ K L := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

def reorderedCross (K L : SSet.{0}) :=
  SimplicialChainCross.cross ((Δ[1] : SSet.{0}) ⊗ K) L ≫
    SSet.chainComplexMap (reorder K L) coeff

theorem zero_cross (K L : SSet.{0}) :
    (SSet.chainComplexMap (SSet.ι₀ ≫ swap K) coeff ⊗ₘ 𝟙 (L.chainComplex coeff)) ≫
      reorderedCross K L = SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₀ K L) coeff := by
  rw [reorderedCross, ← Category.assoc, FirstFactorTensorPrismNaturality.cross_identity_right,
    Category.assoc, ← CategoryTheory.Functor.map_comp, zero_reorder]

theorem one_cross (K L : SSet.{0}) :
    (SSet.chainComplexMap (SSet.ι₁ ≫ swap K) coeff ⊗ₘ 𝟙 (L.chainComplex coeff)) ≫
      reorderedCross K L = SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₁ K L) coeff := by
  rw [reorderedCross, ← Category.assoc, FirstFactorTensorPrismNaturality.cross_identity_right,
    Category.assoc, ← CategoryTheory.Functor.map_comp, one_reorder]

theorem reordered_cross_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    (SSet.chainComplexMap (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ f) coeff ⊗ₘ SSet.chainComplexMap g coeff) ≫
      reorderedCross K' L' = reorderedCross K L ≫
        SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff := by
  rw [reorderedCross, reorderedCross, ← Category.assoc, SimplicialChainCross.naturality,
    Category.assoc, ← CategoryTheory.Functor.map_comp, reorder_naturality,
    CategoryTheory.Functor.map_comp, Category.assoc]

def tensorPrism (K L : SSet.{0}) : Homotopy
    (SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₀ K L) coeff)
    (SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₁ K L) coeff) :=
  (Homotopy.ofEq (zero_cross K L).symm).trans
    (((FirstFactorTensorPrismNaturality.prism ((secondCylinder K).chainComplexMap coeff)
      (L.chainComplex coeff)).compRight (reorderedCross K L)).trans
        (Homotopy.ofEq (one_cross K L)))

theorem tensor_hom (K L : SSet.{0}) (N : ℕ) :
    (tensorPrism K L).hom N (N + 1) =
    (FirstFactorTensorPrismNaturality.prism ((secondCylinder K).chainComplexMap coeff)
      (L.chainComplex coeff)).hom N (N + 1) ≫ (reorderedCross K L).f (N + 1) := by
  simp only [tensorPrism, Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply,
    Homotopy.compRight_hom, zero_add, add_zero]

theorem tensor_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') (N : ℕ) :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f N ≫
      (tensorPrism K' L').hom N (N + 1) =
    (tensorPrism K L).hom N (N + 1) ≫
      (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (N + 1) := by
  have ht := FirstFactorTensorPrismNaturality.naturality
    ((secondCylinder K).chainComplexMap coeff) ((secondCylinder K').chainComplexMap coeff)
    (SSet.chainComplexMap f coeff) (SSet.chainComplexMap (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ f) coeff)
    (SSet.chainComplexMap g coeff) (fun j => second_prism_naturality f j (j + 1)) N
  have hs := congrArg (fun h => h.f (N + 1)) (reordered_cross_naturality f g)
  simp only [HomologicalComplex.comp_f] at hs
  rw [tensor_hom, tensor_hom, ← Category.assoc, ht, Category.assoc, hs, Category.assoc]

def difference (N : ℕ) (K L : SSet.{0}) :
    (K.chainComplex coeff ⊗ L.chainComplex coeff).X N ⟶ ((target K L).chainComplex coeff).X (N + 1) :=
  (SimplicialTimeModelComparison.productPrism K L).hom N (N + 1) - (tensorPrism K L).hom N (N + 1)

theorem difference_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') (N : ℕ) :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f N ≫ difference N K' L' =
    difference N K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (N + 1) := by
  simp only [difference, Preadditive.comp_sub, Preadditive.sub_comp,
    SimplicialTimeModelComparison.product_naturality, tensor_naturality]

theorem difference_zero (K L : SSet.{0}) :
    difference 0 K L ≫ ((target K L).chainComplex coeff).d 1 0 = 0 := by
  simp only [difference, Preadditive.sub_comp]
  rw [SimplicialTimeModelComparison.homotopy_boundary_zero,
    SimplicialTimeModelComparison.homotopy_boundary_zero, sub_self]

theorem difference_comm (N : ℕ) (K L : SSet.{0}) :
    difference (N + 1) K L ≫ ((target K L).chainComplex coeff).d (N + 2) (N + 1) =
      -((K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫ difference N K L) := by
  have hh : (K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫ difference N K L +
      difference (N + 1) K L ≫ ((target K L).chainComplex coeff).d (N + 2) (N + 1) = 0 := by
    calc
      _ = ((K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫
          (SimplicialTimeModelComparison.productPrism K L).hom N (N + 1) +
          (SimplicialTimeModelComparison.productPrism K L).hom (N + 1) (N + 2) ≫
          ((target K L).chainComplex coeff).d (N + 2) (N + 1)) -
        ((K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫
          (tensorPrism K L).hom N (N + 1) + (tensorPrism K L).hom (N + 1) (N + 2) ≫
          ((target K L).chainComplex coeff).d (N + 2) (N + 1)) := by
        simp only [difference, Preadditive.comp_sub, Preadditive.sub_comp]
        abel
      _ = 0 := by rw [SimplicialTimeModelComparison.homotopy_boundary,
        SimplicialTimeModelComparison.homotopy_boundary, sub_self]
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hh

def doublePrism (N : ℕ) (K L : SSet.{0}) :
    (K.chainComplex coeff ⊗ L.chainComplex coeff).X N ⟶ ((target K L).chainComplex coeff).X (N + 2) :=
  NaturalDegreeOneFilling.doublePrism difference N K L

theorem double_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') (N : ℕ) :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f N ≫ doublePrism N K' L' =
    doublePrism N K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (N + 2) :=
  NaturalDegreeOneFilling.naturality difference N f g

theorem cycle_boundary (N : ℕ) (K L : SSet.{0}) :
    (K.chainComplex coeff ⊗ L.chainComplex coeff).iCycles N ≫
      ((SimplicialTimeModelComparison.productPrism K L).hom N (N + 1) - (tensorPrism K L).hom N (N + 1)) =
    ((K.chainComplex coeff ⊗ L.chainComplex coeff).iCycles N ≫ doublePrism N K L) ≫
      ((target K L).chainComplex coeff).d (N + 2) (N + 1) :=
  NaturalDegreeOneFilling.cycle_boundary difference
    (fun N {K K' L L'} f g => difference_naturality f g N) difference_zero difference_comm N K L

end
end Finsler.FirstFactorSimplicialTimeModelComparison
