module

public import Finsler.Topology.SimplicialTimeCylinder
public import Finsler.Topology.SimplicialChainCross
public import Finsler.Topology.TensorIdentityPrismNaturality
public import Finsler.Topology.NaturalDegreeOneFilling

/-! Instantiate the constructive natural double prism with the two
actual simplicial time models. Endpoint equality, naturality and the
full differential identities are proved from the actual cylinder and
shuffle maps. Their difference on every input cycle has a concrete
natural degree-two filling, including input degree zero. -/

@[expose] public section
namespace Finsler.SimplicialTimeModelComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SSet
open Finsler.CochainComparison Finsler.TripleTimeModelExtension Finsler.SimplicialTimeCylinder
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

def productPrism (K L : SSet.{0}) : Homotopy
    (SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₀ K L) coeff)
    (SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₁ K L) coeff) :=
  ((productCylinder K L).chainComplexMap coeff).compLeft (SimplicialChainCross.cross K L)

def tensorPrism (K L : SSet.{0}) : Homotopy
    (SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₀ K L) coeff)
    (SimplicialChainCross.cross K L ≫ SSet.chainComplexMap (face₁ K L) coeff) :=
  (Homotopy.ofEq (SimplicialChainCross.identity_left (K := K) (SSet.ι₀ ≫ swap L)).symm).trans
    (((TensorIdentityPrismNaturality.prism (K.chainComplex coeff)
      ((secondCylinder L).chainComplexMap coeff)).compRight
        (SimplicialChainCross.cross K ((Δ[1] : SSet.{0}) ⊗ L))).trans
      (Homotopy.ofEq (SimplicialChainCross.identity_left (K := K) (SSet.ι₁ ≫ swap L))))

theorem tensor_hom (K L : SSet.{0}) (N : ℕ) :
    (tensorPrism K L).hom N (N + 1) =
    (TensorIdentityPrismNaturality.prism (K.chainComplex coeff)
      ((secondCylinder L).chainComplexMap coeff)).hom N (N + 1) ≫
      (SimplicialChainCross.cross K ((Δ[1] : SSet.{0}) ⊗ L)).f (N + 1) := by
  simp only [tensorPrism, Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply,
    Homotopy.compRight_hom, zero_add, add_zero]

theorem product_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') (N : ℕ) :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f N ≫
      (productPrism K' L').hom N (N + 1) =
    (productPrism K L).hom N (N + 1) ≫
      (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (N + 1) := by
  have hs : (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f N ≫
      (SimplicialChainCross.cross K' L').f N =
      (SimplicialChainCross.cross K L).f N ≫ (SSet.chainComplexMap (f ⊗ₘ g) coeff).f N := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun h => h.f N)
      (SimplicialChainCross.naturality f g)
  change _ ≫ ((SimplicialChainCross.cross K' L').f N ≫
    ((productCylinder K' L').chainComplexMap coeff).hom N (N + 1)) =
    ((SimplicialChainCross.cross K L).f N ≫ ((productCylinder K L).chainComplexMap coeff).hom N (N + 1)) ≫ _
  rw [← Category.assoc, hs, Category.assoc, product_prism_naturality, Category.assoc]

theorem tensor_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') (N : ℕ) :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f N ≫
      (tensorPrism K' L').hom N (N + 1) =
    (tensorPrism K L).hom N (N + 1) ≫
      (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (N + 1) := by
  have ht := TensorIdentityPrismNaturality.naturality
    ((secondCylinder L).chainComplexMap coeff) ((secondCylinder L').chainComplexMap coeff)
    (SSet.chainComplexMap f coeff) (SSet.chainComplexMap g coeff)
    (SSet.chainComplexMap (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g) coeff)
    (fun k => second_prism_naturality g k (k + 1)) N
  have hs : (SSet.chainComplexMap f coeff ⊗ₘ
      SSet.chainComplexMap (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g) coeff).f (N + 1) ≫
      (SimplicialChainCross.cross K' ((Δ[1] : SSet.{0}) ⊗ L')).f (N + 1) =
      (SimplicialChainCross.cross K ((Δ[1] : SSet.{0}) ⊗ L)).f (N + 1) ≫
        (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (N + 1) := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun h => h.f (N + 1))
      (SimplicialChainCross.naturality f (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g))
  rw [tensor_hom, tensor_hom, ← Category.assoc, ht, Category.assoc, hs, Category.assoc]

def difference (N : ℕ) (K L : SSet.{0}) :
    (K.chainComplex coeff ⊗ L.chainComplex coeff).X N ⟶ ((target K L).chainComplex coeff).X (N + 1) :=
  (productPrism K L).hom N (N + 1) - (tensorPrism K L).hom N (N + 1)

theorem difference_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') (N : ℕ) :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f N ≫ difference N K' L' =
    difference N K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (N + 1) := by
  simp only [difference, Preadditive.comp_sub, Preadditive.sub_comp, product_naturality, tensor_naturality]

private theorem homotopy_boundary {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : C ⟶ D} (H : Homotopy f₀ f₁) (N : ℕ) :
    C.d (N + 1) N ≫ H.hom N (N + 1) + H.hom (N + 1) (N + 2) ≫ D.d (N + 2) (N + 1) =
      f₀.f (N + 1) - f₁.f (N + 1) := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using (H.comm (N + 1)).symm

private theorem homotopy_boundary_zero {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : C ⟶ D} (H : Homotopy f₀ f₁) :
    H.hom 0 1 ≫ D.d 1 0 = f₀.f 0 - f₁.f 0 := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] using (H.comm 0).symm

theorem difference_zero (K L : SSet.{0}) :
    difference 0 K L ≫ ((target K L).chainComplex coeff).d 1 0 = 0 := by
  simp only [difference, Preadditive.sub_comp]
  rw [homotopy_boundary_zero, homotopy_boundary_zero, sub_self]

theorem difference_comm (N : ℕ) (K L : SSet.{0}) :
    difference (N + 1) K L ≫ ((target K L).chainComplex coeff).d (N + 2) (N + 1) =
      -((K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫ difference N K L) := by
  have hh : (K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫ difference N K L +
      difference (N + 1) K L ≫ ((target K L).chainComplex coeff).d (N + 2) (N + 1) = 0 := by
    calc
      _ = ((K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫
          (productPrism K L).hom N (N + 1) + (productPrism K L).hom (N + 1) (N + 2) ≫
          ((target K L).chainComplex coeff).d (N + 2) (N + 1)) -
        ((K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫
          (tensorPrism K L).hom N (N + 1) + (tensorPrism K L).hom (N + 1) (N + 2) ≫
          ((target K L).chainComplex coeff).d (N + 2) (N + 1)) := by
        simp only [difference, Preadditive.comp_sub, Preadditive.sub_comp]
        abel
      _ = 0 := by rw [homotopy_boundary, homotopy_boundary, sub_self]
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
      ((productPrism K L).hom N (N + 1) - (tensorPrism K L).hom N (N + 1)) =
    ((K.chainComplex coeff ⊗ L.chainComplex coeff).iCycles N ≫ doublePrism N K L) ≫
      ((target K L).chainComplex coeff).d (N + 2) (N + 1) :=
  NaturalDegreeOneFilling.cycle_boundary difference
    (fun N {K K' L L'} f g => difference_naturality f g N) difference_zero difference_comm N K L

end
end Finsler.SimplicialTimeModelComparison
