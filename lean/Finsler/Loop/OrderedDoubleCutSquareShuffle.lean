module

public import Finsler.Loop.OrderedDoubleCutTriangle
public import Finsler.Topology.PrismShuffle

/-! The TWO triangles below are the ACTUAL (1,1) shuffle of the
original canonical interval simplex. No replacement two-chain is
silently substituted for that square. -/
@[expose] public section
namespace Finsler.OrderedDoubleCutSquareShuffle
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Convexity
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

abbrev square := OrderedDoubleCutTimes.square

def classifying : (Δ[1] : SSet.{0}) ⊗ Δ[1] ⟶ TopCat.toSSet.obj square :=
  (SSet.yonedaEquiv.symm TimeShuffleComparison.intervalSimplex ⊗ₘ
    SSet.yonedaEquiv.symm TimeShuffleComparison.intervalSimplex) ≫
      Functor.LaxMonoidal.μ TopCat.toSSet TopCat.I TopCat.I

theorem top_fst_evaluate (v : square) : (fst TopCat.I TopCat.I) v = v.1 := rfl
theorem top_snd_evaluate (v : square) : (snd TopCat.I TopCat.I) v = v.2 := rfl
theorem type_fst_evaluate {A B : Type} (a : A) (b : B) : (fst A B) (a, b) = a := rfl
theorem type_snd_evaluate {A B : Type} (a : A) (b : B) : (snd A B) (a, b) = b := rfl

theorem degeneracy_coordinate (i : Fin 2) (z : StdSimplex ℝ (Fin 3)) :
    (((TopCat.I.toSSetObjEquiv _)
      ((TopCat.toSSet.obj TopCat.I).σ i TimeShuffleComparison.intervalSimplex) z).down : ℝ) =
      (StdSimplex.map i.predAbove z).weights 1 := by
  rw [IntervalTriangle.canonical_simplex]
  change ((IntervalTriangle.intervalMap (StdSimplex.map i.predAbove z)).down : ℝ) = _
  exact IntervalTriangle.interval_coordinate _

theorem mapped_weight (f : Fin 3 → Fin 2) (z : StdSimplex ℝ (Fin 3)) :
    (StdSimplex.map f z).weights 1 = ∑ i : Fin 3, if f i = 1 then z.weights i else 0 := by
  simp [StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.single_apply]

theorem early_coordinate (z : StdSimplex ℝ (Fin 3)) :
    (StdSimplex.map (0 : Fin 2).predAbove z).weights 1 = z.weights 2 := by
  rw [mapped_weight, Fin.sum_univ_three]
  norm_num [Fin.predAbove]

theorem late_coordinate (z : StdSimplex ℝ (Fin 3)) :
    (StdSimplex.map (1 : Fin 2).predAbove z).weights 1 = z.weights 1 + z.weights 2 := by
  rw [mapped_weight, Fin.sum_univ_three]
  norm_num [Fin.predAbove]

theorem rect_zero : PrismShuffle.rect 1 0 =
    ((Δ[1] : SSet.{0}).σ 0 (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)),
     (Δ[1] : SSet.{0}).σ 1 (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) := by
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl

theorem rect_one : PrismShuffle.rect 1 1 =
    ((Δ[1] : SSet.{0}).σ 1 (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)),
     (Δ[1] : SSet.{0}).σ 0 (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) := by
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl

theorem mu_evaluate (q : ℕ) (a b : TopCat.toSSet.obj TopCat.I _⦋q⦌)
    (z : StdSimplex ℝ (Fin (q + 1))) :
    square.toSSetObjEquiv _
      ((Functor.LaxMonoidal.μ TopCat.toSSet TopCat.I TopCat.I).app _ (a, b)) z =
      (TopCat.I.toSSetObjEquiv _ a z, TopCat.I.toSSetObjEquiv _ b z) := by
  apply Prod.ext
  · have h := congrArg (fun f => f.app _ (a, b))
      (Functor.Monoidal.μ_fst TopCat.toSSet TopCat.I TopCat.I)
    have hfa : (fst (TopCat.toSSet.obj TopCat.I _⦋q⦌)
      (TopCat.toSSet.obj TopCat.I _⦋q⦌)) (a, b) = a := rfl
    have he := congrArg (fun τ => TopCat.I.toSSetObjEquiv _ τ z) h
    simp only [NatTrans.comp_app, types_comp_apply,
      TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply,
      CategoryTheory.Functor.Monoidal.fst_app, top_fst_evaluate] at he
    exact he.trans (congrArg (fun τ => TopCat.I.toSSetObjEquiv _ τ z) hfa)
  · have h := congrArg (fun f => f.app _ (a, b))
      (Functor.Monoidal.μ_snd TopCat.toSSet TopCat.I TopCat.I)
    have hsb : (snd (TopCat.toSSet.obj TopCat.I _⦋q⦌)
      (TopCat.toSSet.obj TopCat.I _⦋q⦌)) (a, b) = b := rfl
    have he := congrArg (fun τ => TopCat.I.toSSetObjEquiv _ τ z) h
    simp only [NatTrans.comp_app, types_comp_apply,
      TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply,
      CategoryTheory.Functor.Monoidal.snd_app, top_snd_evaluate] at he
    exact he.trans (congrArg (fun τ => TopCat.I.toSSetObjEquiv _ τ z) hsb)

theorem classifying_degeneracies (i j : Fin 2) :
    classifying.app _
      ((Δ[1] : SSet.{0}).σ i (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)),
       (Δ[1] : SSet.{0}).σ j (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) =
    (Functor.LaxMonoidal.μ TopCat.toSSet TopCat.I TopCat.I).app _
      ((TopCat.toSSet.obj TopCat.I).σ i TimeShuffleComparison.intervalSimplex,
       (TopCat.toSSet.obj TopCat.I).σ j TimeShuffleComparison.intervalSimplex) := by
  change (Functor.LaxMonoidal.μ TopCat.toSSet TopCat.I TopCat.I).app _
    ((SSet.yonedaEquiv.symm TimeShuffleComparison.intervalSimplex).app _
       ((Δ[1] : SSet.{0}).σ i (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))),
     (SSet.yonedaEquiv.symm TimeShuffleComparison.intervalSimplex).app _
       ((Δ[1] : SSet.{0}).σ j (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)))) = _
  rw [SSet.σ_naturality_apply, SSet.σ_naturality_apply]
  have hi : (SSet.yonedaEquiv.symm TimeShuffleComparison.intervalSimplex).app _
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = TimeShuffleComparison.intervalSimplex :=
    SSet.yonedaEquiv.apply_symm_apply TimeShuffleComparison.intervalSimplex
  rw [hi]

theorem simplex_map_identity (z : StdSimplex ℝ (Fin 3)) :
    UniversalTimeTriangle.simplexMap z = z := by
  simp only [UniversalTimeTriangle.simplexMap, ContinuousMap.comp_apply, ContinuousMap.id_apply,
    StdSimplex.continuousAffineMapMk_apply, StdSimplex.affineMapMk_apply,
    StdSimplex.iConvexComb_single]

theorem simplex_zero : classifying.app _ (PrismShuffle.rect 1 0) =
    (TopCat.toSSet.map OrderedDoubleCutTriangle.upper).app _ UniversalTimeTriangle.simplex := by
  apply (square.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro z
  rw [rect_zero, classifying_degeneracies, mu_evaluate,
    TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  simp only [UniversalTimeTriangle.simplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  rw [simplex_map_identity]
  apply Prod.ext <;> apply ULift.ext <;> apply Subtype.ext
  · rw [degeneracy_coordinate, early_coordinate]
    rfl
  · rw [degeneracy_coordinate, late_coordinate]
    rfl

theorem simplex_one : classifying.app _ (PrismShuffle.rect 1 1) =
    (TopCat.toSSet.map OrderedDoubleCutTriangle.lower).app _ UniversalTimeTriangle.simplex := by
  apply (square.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro z
  rw [rect_one, classifying_degeneracies, mu_evaluate,
    TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  simp only [UniversalTimeTriangle.simplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  rw [simplex_map_identity]
  apply Prod.ext <;> apply ULift.ext <;> apply Subtype.ext
  · rw [degeneracy_coordinate, late_coordinate]
    rfl
  · rw [degeneracy_coordinate, early_coordinate]
    rfl

def squareChain : coeff ⟶ (chains square).X 2 :=
  (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫
    SingularChainCross.right TopCat.I TopCat.I 1 1 TimeShuffleComparison.intervalSimplex

theorem square_split : squareChain =
    (TopCat.toSSet.obj UniversalTimeTriangle.space).ιChainComplex UniversalTimeTriangle.simplex ≫
      (push OrderedDoubleCutTriangle.lower).f 2 +
    (TopCat.toSSet.obj UniversalTimeTriangle.space).ιChainComplex UniversalTimeTriangle.simplex ≫
      (push OrderedDoubleCutTriangle.upper).f 2 := by
  rw [squareChain, SingularChainCross.right_simplex, PrismShuffle.shuffle_one,
    Fin.sum_univ_two, Preadditive.add_comp]
  change _ ≫ (SSet.chainComplexMap classifying coeff).f 2 +
    _ ≫ (SSet.chainComplexMap classifying coeff).f 2 = _
  rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f, simplex_zero, simplex_one]
  simp only [push, ← SSet.ι_chainComplexMap_f]
  exact add_comm _ _

end
end Finsler.OrderedDoubleCutSquareShuffle
