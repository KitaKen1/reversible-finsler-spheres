module

public import Finsler.Topology.TripleTimeModelExtension
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-! The actual simplicial product-time and second-input-time cylinders.
Their parameter maps and naturality squares are literal coordinate
permutations; the induced chain-prism naturality uses Tau Ceti's actual
commutative-square theorem. -/

@[expose] public section
namespace Finsler.SimplicialTimeCylinder

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SSet
open Finsler.CochainComparison Finsler.TripleTimeModelExtension
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

def cylinderOfMap {X Y : SSet.{0}} (f : X ⊗ Δ[1] ⟶ Y) :
    SSet.Homotopy (SSet.ι₀ ≫ f) (SSet.ι₁ ≫ f) where
  h := f
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

def swap (L : SSet.{0}) : L ⊗ Δ[1] ⟶ Δ[1] ⊗ L := (β_ L (Δ[1] : SSet.{0})).hom

def reorder (K L : SSet.{0}) : (K ⊗ L) ⊗ Δ[1] ⟶ target K L :=
  (α_ K L (Δ[1] : SSet.{0})).hom ≫ (𝟙 K ⊗ₘ swap L)

def face₀ (K L : SSet.{0}) : K ⊗ L ⟶ target K L := 𝟙 K ⊗ₘ (SSet.ι₀ ≫ swap L)
def face₁ (K L : SSet.{0}) : K ⊗ L ⟶ target K L := 𝟙 K ⊗ₘ (SSet.ι₁ ≫ swap L)

theorem zero_reorder (K L : SSet.{0}) : SSet.ι₀ ≫ reorder K L = face₀ K L := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem one_reorder (K L : SSet.{0}) : SSet.ι₁ ≫ reorder K L = face₁ K L := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

def productCylinder (K L : SSet.{0}) : SSet.Homotopy (face₀ K L) (face₁ K L) where
  h := reorder K L
  h₀ := zero_reorder K L
  h₁ := one_reorder K L
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

def secondCylinder (L : SSet.{0}) : SSet.Homotopy (SSet.ι₀ ≫ swap L) (SSet.ι₁ ≫ swap L) :=
  cylinderOfMap (swap L)

theorem reorder_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    ((f ⊗ₘ g) ▷ Δ[1]) ≫ reorder K' L' =
      reorder K L ≫ (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem swap_naturality {L L' : SSet.{0}} (g : L ⟶ L') :
    (g ▷ Δ[1]) ≫ swap L' = swap L ≫ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem product_prism_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') (p q : ℕ) :
    (SSet.chainComplexMap (f ⊗ₘ g) coeff).f p ≫
      ((productCylinder K' L').chainComplexMap coeff).hom p q =
    ((productCylinder K L).chainComplexMap coeff).hom p q ≫
      (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f q :=
  SSet.Homotopy.chainComplexMap_hom_comm (productCylinder K L) (productCylinder K' L')
    (reorder_naturality f g) coeff p q

theorem second_prism_naturality {L L' : SSet.{0}} (g : L ⟶ L') (p q : ℕ) :
    (SSet.chainComplexMap g coeff).f p ≫ ((secondCylinder L').chainComplexMap coeff).hom p q =
      ((secondCylinder L).chainComplexMap coeff).hom p q ≫
        (SSet.chainComplexMap (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g) coeff).f q :=
  SSet.Homotopy.chainComplexMap_hom_comm (secondCylinder L) (secondCylinder L')
    (swap_naturality g) coeff p q

end
end Finsler.SimplicialTimeCylinder
