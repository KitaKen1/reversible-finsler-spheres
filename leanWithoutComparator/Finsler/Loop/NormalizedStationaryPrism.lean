module

public import Finsler.Topology.ShuffleBlockNormalization
public import Finsler.Topology.TimePrismNaturality

/-! A genuinely stationary topological homotopy has only degenerate
actual prism simplices. Its ACTUAL singular prism is killed by
cochain normalization. This is a chain statement, including degree0. -/
@[expose] public section
namespace Finsler.NormalizedStationaryPrism
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial DoldKan
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def stationary {X Y : TopCat.{0}} (f : X ⟶ Y) : TopCat.Homotopy f f := TopCat.Homotopy.refl f

theorem stationary_toSSet {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (stationary f).toSSet.h =
      fst (TopCat.toSSet.obj X) (Δ[1] : SSet.{0}) ≫ TopCat.toSSet.map f := by
  have hh : (stationary f).h = fst X TopCat.I ≫ f := rfl
  simp only [TopCat.Homotopy.toSSet, hh, Functor.map_comp, ← Category.assoc,
    Functor.Monoidal.μ_fst, whiskerLeft_fst]

theorem stationary_simplex {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋q⦌) (i : Fin (q + 1)) :
    (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ (stationary f).toSSet.h).app _
        (PrismShuffle.rect q i) =
      (TopCat.toSSet.obj Y).σ i ((TopCat.toSSet.map f).app _ σ) := by
  rw [stationary_toSSet]
  have hc : SSet.yonedaEquiv.symm σ ▷ (Δ[1] : SSet.{0}) ≫
      (fst (TopCat.toSSet.obj X) Δ[1] ≫ TopCat.toSSet.map f) =
    fst (Δ[q] : SSet.{0}) Δ[1] ≫ (SSet.yonedaEquiv.symm σ ≫ TopCat.toSSet.map f) := by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
  rw [hc]
  change (SSet.yonedaEquiv.symm σ ≫ TopCat.toSSet.map f).app _ (PrismShuffle.rect q i).1 = _
  change (SSet.yonedaEquiv.symm σ ≫ TopCat.toSSet.map f).app _
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ i)) = _
  rw [NatTrans.comp_app, types_comp_apply, SSet.yonedaEquiv_symm_app_objEquiv_symm]
  exact SSet.σ_naturality_apply (TopCat.toSSet.map f) i σ

theorem stationary_prism_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (q + 1)) :
    ((stationary f).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      SingularNormalization.normalize Y (q + 1) φ = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  rw [← Category.assoc, PrismRectangle.prism_simplex, PrismShuffle.shuffle_one]
  simp only [Preadditive.sum_comp,
    SSet.ι_chainComplexMap_f, stationary_simplex]
  apply Finset.sum_eq_zero
  intro i _
  exact ShuffleBlockNormalization.normalize_simplex_zero Y (q + 1) φ _
    ((TopCat.toSSet.obj Y).σ_mem_degenerate i _)

theorem stationary_on_subspace {A X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (e : A ⟶ X)
    (hH : ∀ (v : _root_.unitInterval) (a : A), H (v, e a) = f (e a))
    (q : ℕ) (φ : singularCochainGroup (ZMod 2) Y (q + 1)) :
    (push e).f q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      SingularNormalization.normalize Y (q + 1) φ = 0 := by
  have he : (H.comp (TopCat.Homotopy.refl e)).h = (stationary (e ≫ f)).h := by
    apply TopCat.ext
    intro z
    exact hH z.2.down z.1
  have hp := TimePrismNaturality.prism_congr (H.comp (TopCat.Homotopy.refl e))
    (stationary (e ≫ f)) he q
  rw [← Category.assoc, TimePrismNaturality.prism_pre, hp]
  exact stationary_prism_zero (e ≫ f) q φ

end
end Finsler.NormalizedStationaryPrism
