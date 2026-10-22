module

public import Finsler.Topology.TripleStandardCone
public import TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber
import all TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber

/-! Extend concrete chains in the three-factor standard time models
to genuine natural maps on all simplicial input tensor chains. This
adapts Tau Ceti's acyclic-model extension to target K times Delta[1]
times L and permits the degree-two fillings required for time-model
comparison. No arbitrary filling or shuffle associativity is assumed. -/

@[expose] public section
namespace Finsler.TripleTimeModelExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SSet
open Finsler.CochainComparison
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

def target (K L : SSet.{0}) : SSet.{0} := K ⊗ (Δ[1] ⊗ L)

def classify {K L : SSet.{0}} {p q : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) :
    TripleStandardCone.model p q ⟶ target K L :=
  SSet.yonedaEquiv.symm x ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ SSet.yonedaEquiv.symm y)

theorem classify_naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L')
    {p q : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) :
    classify x y ≫ (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) =
      classify (f.app _ x) (g.app _ y) := by
  simp only [classify, tensorHom_comp_tensorHom, Category.id_comp,
    SSet.yonedaEquiv_symm_comp]

def extend {n r : ℕ}
    (c : ∀ p q : ℕ, p + q = n →
      (coeff ⊗ coeff ⟶ ((TripleStandardCone.model p q).chainComplex coeff).X r))
    (K L : SSet.{0}) :
    (K.chainComplex coeff ⊗ L.chainComplex coeff).X n ⟶ ((target K L).chainComplex coeff).X r :=
  mapBifunctorDesc fun p q h => tensorChainComplexXDesc fun x y =>
    c p q h ≫ (SSet.chainComplexMap (classify x y) coeff).f r

@[reassoc]
theorem ι_extend {n r : ℕ}
    (c : ∀ p q : ℕ, p + q = n →
      (coeff ⊗ coeff ⟶ ((TripleStandardCone.model p q).chainComplex coeff).X r))
    {K L : SSet.{0}} {p q : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n) :
    (K.ιChainComplex (R := coeff) x ⊗ₘ L.ιChainComplex (R := coeff) y) ≫
      ιTensorObj _ _ p q n h ≫ extend c K L =
    c p q h ≫ (SSet.chainComplexMap (classify x y) coeff).f r := by
  simp [extend]

theorem naturality {n r : ℕ}
    (c : ∀ p q : ℕ, p + q = n →
      (coeff ⊗ coeff ⟶ ((TripleStandardCone.model p q).chainComplex coeff).X r))
    {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f n ≫ extend c K' L' =
      extend c K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f r := by
  refine mapBifunctor.hom_ext fun p q h => tensorChainComplexX_hom_ext fun x y => ?_
  simp only [SSet.tensorHom_ιTensorObj_tensorHom_f_assoc, ι_extend, ι_extend_assoc]
  have hc := congrArg (fun t => (SSet.chainComplexMap t coeff).f r)
    (classify_naturality f g x y)
  rw [← TauCeti.SSet.chainComplexMap_f_comp] at hc
  simpa only [Category.assoc] using congrArg (fun t => c p q h ≫ t) hc.symm

theorem extend_zero (n r : ℕ) (K L : SSet.{0}) :
    extend (fun p q (_ : p + q = n) =>
      (0 : coeff ⊗ coeff ⟶ ((TripleStandardCone.model p q).chainComplex coeff).X r)) K L = 0 := by
  refine mapBifunctor.hom_ext fun p q h => tensorChainComplexX_hom_ext fun x y => ?_
  rw [ι_extend, zero_comp, comp_zero, comp_zero]

theorem classify_top (p q : ℕ) :
    classify (SSet.yonedaEquiv (𝟙 (Δ[p] : SSet.{0})))
      (SSet.yonedaEquiv (𝟙 (Δ[q] : SSet.{0}))) = 𝟙 (TripleStandardCone.model p q) := by
  simp only [classify, Equiv.symm_apply_apply, id_tensorHom_id]
  rfl

theorem model_value {n r : ℕ}
    (c : ∀ p q : ℕ, p + q = n →
      (coeff ⊗ coeff ⟶ ((TripleStandardCone.model p q).chainComplex coeff).X r))
    (p q : ℕ) (h : p + q = n) :
    ((Δ[p] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _)) ⊗ₘ
      (Δ[q] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _))) ≫
      ιTensorObj _ _ p q n h ≫ extend c (Δ[p]) (Δ[q]) = c p q h := by
  rw [ι_extend, classify_top]
  change c p q h ≫ (((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map
    (𝟙 (TripleStandardCone.model p q))).f r = _
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.comp_id]

theorem determined {n r : ℕ}
    (u : ∀ K L : SSet.{0}, (K.chainComplex coeff ⊗ L.chainComplex coeff).X n ⟶
      ((target K L).chainComplex coeff).X r)
    (hu : ∀ ⦃K K' L L' : SSet.{0}⦄ (f : K ⟶ K') (g : L ⟶ L'),
      (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f n ≫ u K' L' =
        u K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f r)
    {K L : SSet.{0}} {p q : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (h : p + q = n) :
    (K.ιChainComplex (R := coeff) x ⊗ₘ L.ιChainComplex (R := coeff) y) ≫
      ιTensorObj _ _ p q n h ≫ u K L =
    ((Δ[p] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _)) ⊗ₘ
      (Δ[q] : SSet.{0}).ιChainComplex (R := coeff) (SSet.yonedaEquiv (𝟙 _))) ≫
      ιTensorObj _ _ p q n h ≫ u (Δ[p]) (Δ[q]) ≫
        (SSet.chainComplexMap (classify x y) coeff).f r := by
  rw [← Category.assoc, SSet.tensorHom_ιTensorObj_eq_model, Category.assoc, Category.assoc, hu]
  rfl

end
end Finsler.TripleTimeModelExtension
