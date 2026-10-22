module

public import Finsler.Topology.SingularRightNaturality

/-! Naturality of actual fixed-right-simplex shuffle insertion in
its SOURCE factor. In particular the moving time triangle retains
any independent source-boundary subspace, before any cap operation. -/
@[expose] public section
namespace Finsler.SingularLeftNaturality
open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem right_pre (X X' Y : TopCat.{0}) (f : X ⟶ X') (p q : ℕ)
    (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    (SupportedCapNaturality.push f).f p ≫ SingularChainCross.right X' Y p q τ =
      SingularChainCross.right X Y p q τ ≫ (SupportedCapNaturality.push (f ▷ Y)).f (p + q) := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  have hm : ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X Y) ≫ TopCat.toSSet.map (f ▷ Y) =
      (SSet.yonedaEquiv.symm ((TopCat.toSSet.map f).app _ σ) ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
        Functor.LaxMonoidal.μ TopCat.toSSet X' Y := by
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, ← Functor.LaxMonoidal.μ_natural_left]
    simp only [tensorHom_def', comp_whiskerRight, Category.assoc]
  rw [← Category.assoc, SupportedCapNaturality.push, SSet.ι_chainComplexMap_f, SingularChainCross.right_simplex]
  rw [← Category.assoc, SingularChainCross.right_simplex, Category.assoc,
    SupportedCapNaturality.push, ← HomologicalComplex.comp_f, ← Functor.map_comp, hm]

end
end Finsler.SingularLeftNaturality
