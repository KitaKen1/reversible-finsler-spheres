module

public import Finsler.Topology.TimeShuffleComparison

/-! Literal precomposition naturality for the actual singular time prism. -/

@[expose] public section
namespace Finsler.TimePrismNaturality

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem toSSet_pre {X Y Z : TopCat.{0}} {f g : Y ⟶ Z}
    (H : TopCat.Homotopy f g) (e : X ⟶ Y) :
    (H.comp (TopCat.Homotopy.refl e)).toSSet.h =
      (TopCat.toSSet.map e ▷ Δ[1]) ≫ H.toSSet.h := by
  have he : (H.comp (TopCat.Homotopy.refl e)).h = (e ▷ TopCat.I) ≫ H.h := by
    ext z : 1
    rfl
  simp only [TopCat.Homotopy.toSSet, he, Functor.map_comp,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, ← whisker_exchange_assoc]

theorem prism_pre {X Y Z : TopCat.{0}} {f g : Y ⟶ Z}
    (H : TopCat.Homotopy f g) (e : X ⟶ Y) (q : ℕ) :
    (SupportedCapNaturality.push e).f q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) =
      ((H.comp (TopCat.Homotopy.refl e)).toSSet.chainComplexMap coeff).hom q (q + 1) := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  rw [← Category.assoc, SupportedCapNaturality.push, SSet.ι_chainComplexMap_f,
    PrismRectangle.prism_simplex, PrismRectangle.prism_simplex]
  rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, ← toSSet_pre]

theorem toSSet_post {X Y Z : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (e : Y ⟶ Z) :
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl e) H).toSSet.h = H.toSSet.h ≫ TopCat.toSSet.map e := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl e) H).h = H.h ≫ e := by ext z : 1; rfl
  simp only [TopCat.Homotopy.toSSet, he, Functor.map_comp, Category.assoc]

theorem prism_post {X Y Z : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (e : Y ⟶ Z) (q : ℕ) :
    (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ (SupportedCapNaturality.push e).f (q + 1) =
      ((TopCat.Homotopy.comp (TopCat.Homotopy.refl e) H).toSSet.chainComplexMap coeff).hom q (q + 1) := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  rw [← Category.assoc, PrismRectangle.prism_simplex, Category.assoc,
    SupportedCapNaturality.push, ← HomologicalComplex.comp_f, ← Functor.map_comp,
    PrismRectangle.prism_simplex, toSSet_post, Category.assoc]

theorem prism_congr {X Y : TopCat.{0}} {f g f' g' : X ⟶ Y}
    (H : TopCat.Homotopy f g) (K : TopCat.Homotopy f' g') (he : H.h = K.h) (q : ℕ) :
    (H.toSSet.chainComplexMap coeff).hom q (q + 1) =
      (K.toSSet.chainComplexMap coeff).hom q (q + 1) := by
  have hs : H.toSSet.h = K.toSSet.h := by simp only [TopCat.Homotopy.toSSet, he]
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  rw [PrismRectangle.prism_simplex, PrismRectangle.prism_simplex, hs]

end
end Finsler.TimePrismNaturality
