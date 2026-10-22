module

public import Finsler.Topology.SingularRightBoundary
public import Finsler.Topology.SupportedCapNaturality

/-! Naturality of the specified singular shuffle insertion in the right
space, including the actual simplex and coefficient multiplication. -/

@[expose] public section
namespace Finsler.SingularRightNaturality

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem right_natural (X Y Z : TopCat.{0}) (f : Y ⟶ Z) (p q : ℕ)
    (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    SingularChainCross.right X Y p q τ ≫
        (SupportedCapNaturality.push (X ◁ f)).f (p + q) =
      SingularChainCross.right X Z p q ((TopCat.toSSet.map f).app _ τ) := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  have hm : ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X Y) ≫ TopCat.toSSet.map (X ◁ f) =
      (SSet.yonedaEquiv.symm σ ⊗ₘ
        SSet.yonedaEquiv.symm ((TopCat.toSSet.map f).app _ τ)) ≫
          Functor.LaxMonoidal.μ TopCat.toSSet X Z := by
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
      ← Functor.LaxMonoidal.μ_natural_right]
    simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc, SingularChainCross.right_simplex, Category.assoc,
    SupportedCapNaturality.push, ← HomologicalComplex.comp_f, ← Functor.map_comp,
    hm, SingularChainCross.right_simplex]

theorem rightChain_map_simplex (X Y Z : TopCat.{0}) (f : Y ⟶ Z) (p q : ℕ)
    (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    SingularRightBoundary.rightChain X Z p q
        ((TopCat.toSSet.obj Y).ιChainComplex τ ≫
          (SupportedCapNaturality.push f).f q) =
      SingularChainCross.right X Y p q τ ≫
        (SupportedCapNaturality.push (X ◁ f)).f (p + q) := by
  rw [SupportedCapNaturality.push, SSet.ι_chainComplexMap_f,
    SingularRightBoundary.rightChain_simplex, right_natural]

end
end Finsler.SingularRightNaturality
