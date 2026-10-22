module

public import Finsler.Topology.CochainComparison
public import TauCeti.AlgebraicTopology.SimplicialSet.Shuffle

/-! A concrete contraction on the standard models Delta[a] times
Delta[1] times Delta[b]. This extends Tau Ceti's componentwise cone and
its chain-boundary proof to the actual three-factor time model.
Every positive-degree cycle has an explicit filling in that model. -/

@[expose] public section
namespace Finsler.TripleStandardCone

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

def model (a b : ℕ) : SSet.{0} := Δ[a] ⊗ (Δ[1] ⊗ Δ[b])

def cone {a b m : ℕ} (x : model a b _⦋m⦌) : model a b _⦋m + 1⦌ :=
  (SSet.stdSimplex.cone x.1, SSet.stdSimplex.prodCone x.2)

theorem δ_zero {a b m : ℕ} (x : model a b _⦋m⦌) :
    (model a b).δ 0 (cone x) = x :=
  Prod.ext (SSet.stdSimplex.δ_zero_cone _) (SSet.stdSimplex.δ_zero_prodCone _)

theorem δ_succ {a b m : ℕ} (x : model a b _⦋m + 1⦌) (i : Fin (m + 2)) :
    (model a b).δ i.succ (cone x) = cone ((model a b).δ i x) :=
  Prod.ext (SSet.stdSimplex.δ_succ_cone _ _) (SSet.stdSimplex.δ_succ_prodCone _ _)

def coneChain (a b m : ℕ) :
    ((model a b).chainComplex coeff).X m ⟶ ((model a b).chainComplex coeff).X (m + 1) :=
  Cofan.IsColimit.desc ((model a b).isColimitChainComplexXCofan coeff m) fun x =>
    (model a b).ιChainComplex (cone x)

@[reassoc (attr := simp)]
theorem ι_coneChain (a b m : ℕ) (x : model a b _⦋m⦌) :
    (model a b).ιChainComplex (R := coeff) x ≫ coneChain a b m =
      (model a b).ιChainComplex (cone x) :=
  Cofan.IsColimit.fac _ _ x

theorem coneChain_d (a b m : ℕ) :
    coneChain a b (m + 1) ≫ ((model a b).chainComplex coeff).d (m + 2) (m + 1) =
    𝟙 _ - ((model a b).chainComplex coeff).d (m + 1) m ≫ coneChain a b m := by
  apply SSet.chainComplex_hom_ext (X := model a b) (R := coeff)
  intro x
  simp only [ι_coneChain_assoc, SSet.ιChainComplex_d, Preadditive.comp_sub,
    Category.comp_id, SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ι_coneChain]
  rw [Fin.sum_univ_succ, δ_zero, Fin.val_zero, pow_zero, one_smul]
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    sub_eq_add_neg]
  refine congrArg (_ + ·) (congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_))
  rw [δ_succ]

theorem cycle_boundary (a b m : ℕ) {M : ModuleCat.{0} (ZMod 2)}
    (c : M ⟶ ((model a b).chainComplex coeff).cycles (m + 1)) :
    c ≫ ((model a b).chainComplex coeff).iCycles (m + 1) =
    (c ≫ ((model a b).chainComplex coeff).iCycles (m + 1) ≫ coneChain a b (m + 1)) ≫
      ((model a b).chainComplex coeff).d (m + 2) (m + 1) := by
  simp only [Category.assoc, coneChain_d, Preadditive.comp_sub,
    Category.comp_id, HomologicalComplex.iCycles_d_assoc, zero_comp, comp_zero, sub_zero]

end
end Finsler.TripleStandardCone
