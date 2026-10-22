module

public import Finsler.Topology.SingularChainCross
public import Finsler.Topology.PrismRectangle
public import Finsler.Topology.SupportedCapNaturality
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! The actual topological homotopy prism is the genuine singular shuffle
cross with the canonical interval simplex, followed by the homotopy map.
The equality includes coefficient multiplication and holds on chains. -/

@[expose] public section
namespace Finsler.TimeShuffleComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def intervalSimplex : TopCat.toSSet.obj TopCat.I.{0} _⦋1⦌ :=
  SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI

theorem interval_classifying : SSet.yonedaEquiv.symm intervalSimplex =
    SSet.stdSimplex.toSSetObjI :=
  SSet.yonedaEquiv.symm_apply_apply _

def rectangle {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (q : ℕ) :
    (chains X).X q ⟶ (chains Y).X (q + 1) :=
  SingularChainCross.right X TopCat.I q 1 intervalSimplex ≫
    (SupportedCapNaturality.push H.h).f (q + 1)

theorem classifying_map {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (q : ℕ) (σ : TopCat.toSSet.obj X _⦋q⦌) :
    ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm intervalSimplex) ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I) ≫ TopCat.toSSet.map H.h =
        SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.toSSet.h := by
  rw [interval_classifying]
  simp only [TopCat.Homotopy.toSSet, ← Category.assoc, tensorHom_def]

theorem rectangle_eq_prism {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (q : ℕ) : rectangle H q = (H.toSSet.chainComplexMap coeff).hom q (q + 1) := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  rw [PrismRectangle.prism_simplex H.toSSet q σ]
  unfold rectangle
  rw [← Category.assoc, SingularChainCross.right_simplex, Category.assoc]
  have hm : (SSet.chainComplexMap
      ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm intervalSimplex) ≫
        Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I) coeff).f (q + 1) ≫
      (SupportedCapNaturality.push H.h).f (q + 1) =
    (SSet.chainComplexMap (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.toSSet.h) coeff).f (q + 1) := by
    unfold SupportedCapNaturality.push
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, classifying_map H q σ]
  rw [hm]

end
end Finsler.TimeShuffleComparison
