module

public import Finsler.Topology.TripleTimeModelExtension

/-! A concrete natural filling of a closed positive-degree family in
K times Delta[1] times L. Fill on the actual standard models by the
proved triple cone, then extend by the classifying maps. This is the
inductive filling step for the difference of the two time prisms. -/

@[expose] public section
namespace Finsler.TripleTimeModelFilling

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SSet
open Finsler.CochainComparison Finsler.TripleTimeModelExtension
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {n : ℕ}
  (u : ∀ K L : SSet.{0}, (K.chainComplex coeff ⊗ L.chainComplex coeff).X n ⟶
    ((target K L).chainComplex coeff).X (n + 1))

def modelValue (p q : ℕ) (h : p + q = n) :
    coeff ⊗ coeff ⟶ ((TripleStandardCone.model p q).chainComplex coeff).X (n + 2) :=
  ((Δ[p] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _)) ⊗ₘ
    (Δ[q] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _))) ≫
    ιTensorObj _ _ p q n h ≫ u (Δ[p]) (Δ[q]) ≫ TripleStandardCone.coneChain p q (n + 1)

def filling (K L : SSet.{0}) :
    (K.chainComplex coeff ⊗ L.chainComplex coeff).X n ⟶
      ((target K L).chainComplex coeff).X (n + 2) :=
  extend (modelValue u) K L

theorem naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f n ≫ filling u K' L' =
      filling u K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (n + 2) :=
  TripleTimeModelExtension.naturality (modelValue u) f g

variable (hclosed : ∀ K L : SSet.{0}, u K L ≫ ((target K L).chainComplex coeff).d (n + 1) n = 0)

include hclosed in
theorem model_boundary (p q : ℕ) (h : p + q = n) :
    modelValue u p q h ≫ ((TripleStandardCone.model p q).chainComplex coeff).d (n + 2) (n + 1) =
    ((Δ[p] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _)) ⊗ₘ
      (Δ[q] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _))) ≫
      ιTensorObj _ _ p q n h ≫ u (Δ[p]) (Δ[q]) := by
  let c : coeff ⊗ coeff ⟶ ((TripleStandardCone.model p q).chainComplex coeff).X (n + 1) :=
    ((Δ[p] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _)) ⊗ₘ
      (Δ[q] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _))) ≫
      ιTensorObj _ _ p q n h ≫ u (Δ[p]) (Δ[q])
  have hc : c ≫ ((TripleStandardCone.model p q).chainComplex coeff).d (n + 1) n = 0 := by
    have hu : u (Δ[p]) (Δ[q]) ≫
        ((TripleStandardCone.model p q).chainComplex coeff).d (n + 1) n = 0 := hclosed (Δ[p]) (Δ[q])
    simp only [c, Category.assoc, hu, comp_zero]
  let z := ((TripleStandardCone.model p q).chainComplex coeff).liftCycles c n
    (by simp [ChainComplex.next_nat_succ]) hc
  have hi : z ≫ ((TripleStandardCone.model p q).chainComplex coeff).iCycles (n + 1) = c :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  have hz := TripleStandardCone.cycle_boundary p q n z
  simp only [← Category.assoc, hi] at hz
  simpa only [modelValue, c, Category.assoc] using hz.symm

include hclosed in
theorem boundary
    (hu : ∀ ⦃K K' L L' : SSet.{0}⦄ (f : K ⟶ K') (g : L ⟶ L'),
      (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f n ≫ u K' L' =
        u K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (n + 1))
    (K L : SSet.{0}) :
    filling u K L ≫ ((target K L).chainComplex coeff).d (n + 2) (n + 1) = u K L := by
  refine mapBifunctor.hom_ext fun p q h => tensorChainComplexX_hom_ext fun x y => ?_
  have hd : (SSet.chainComplexMap (classify x y) coeff).f (n + 2) ≫
      ((target K L).chainComplex coeff).d (n + 2) (n + 1) =
      ((TripleStandardCone.model p q).chainComplex coeff).d (n + 2) (n + 1) ≫
        (SSet.chainComplexMap (classify x y) coeff).f (n + 1) :=
    (SSet.chainComplexMap (classify x y) coeff).comm (n + 2) (n + 1)
  simp only [filling, ι_extend_assoc]
  rw [hd, ← Category.assoc, model_boundary u hclosed]
  exact (TripleTimeModelExtension.determined u hu x y h).symm

end
end Finsler.TripleTimeModelFilling
