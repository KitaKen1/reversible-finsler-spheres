module

public import Finsler.Loop.OrderedDoubleCutSquareShuffle

/-! The ACTUAL boundary of the original shuffle square. The two
interior diagonal edges cancel over F2, leaving all four real sides.
Each side is lifted to the actual boundary subspace. -/
@[expose] public section
namespace Finsler.OrderedSquareBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Convexity
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def side (i : Fin 4) : TopCat.I.{0} ⟶ OrderedDoubleCutTimes.square := TopCat.ofHom
  ⟨fun t => ![(t, 0), (1, t), (t, 1), (0, t)] i, by fin_cases i <;> fun_prop⟩

def diagonal : TopCat.I.{0} ⟶ OrderedDoubleCutTimes.square := TopCat.ofHom
  ⟨fun t => (t, t), continuous_id.prodMk continuous_id⟩

theorem early_on_edge (i : Fin 3) (t : TopCat.I.{0}) :
    ((OrderedDoubleCutTriangle.early (UniversalTimeTriangle.edgeMap i t)).down : ℝ) =
      ![(t.down : ℝ), (t.down : ℝ), 0] i := by
  change (UniversalTimeTriangle.edgeMap i t).weights 2 = _
  have he : UniversalTimeTriangle.edgeMap i t =
      StdSimplex.continuousAffineMapMk (fun j : Fin 2 => StdSimplex.single (R := ℝ) (i.succAbove j))
        (TopCat.stdSimplexHomeomorphI.symm t) := rfl
  rw [he]
  fin_cases i <;> norm_num [StdSimplex.continuousAffineMapMk_apply,
    StdSimplex.weights_affineMapMk_apply, Fin.sum_univ_two, Finsupp.single_apply,
    UniversalTimeTriangle.interval_inverse_weight_zero, UniversalTimeTriangle.interval_inverse_weight_one]

theorem late_on_edge (i : Fin 3) (t : TopCat.I.{0}) :
    ((OrderedDoubleCutTriangle.late (UniversalTimeTriangle.edgeMap i t)).down : ℝ) =
      ![1, (t.down : ℝ), (t.down : ℝ)] i := by
  change (UniversalTimeTriangle.edgeMap i t).weights 1 + (UniversalTimeTriangle.edgeMap i t).weights 2 = _
  have he : UniversalTimeTriangle.edgeMap i t =
      StdSimplex.continuousAffineMapMk (fun j : Fin 2 => StdSimplex.single (R := ℝ) (i.succAbove j))
        (TopCat.stdSimplexHomeomorphI.symm t) := rfl
  rw [he]
  have hv : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  fin_cases i <;> norm_num [StdSimplex.continuousAffineMapMk_apply,
    StdSimplex.weights_affineMapMk_apply, Fin.sum_univ_two, Finsupp.single_apply, hv,
    UniversalTimeTriangle.interval_inverse_weight_zero, UniversalTimeTriangle.interval_inverse_weight_one]

theorem lower_edge (i : Fin 3) : UniversalTimeTriangle.edgeMap i ≫ OrderedDoubleCutTriangle.lower =
    ![side 1, diagonal, side 0] i := by
  apply TopCat.ext
  intro t
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change ((OrderedDoubleCutTriangle.late (UniversalTimeTriangle.edgeMap i t)).down : ℝ) = _
    rw [late_on_edge]
    fin_cases i <;> rfl
  · apply ULift.ext
    apply Subtype.ext
    change ((OrderedDoubleCutTriangle.early (UniversalTimeTriangle.edgeMap i t)).down : ℝ) = _
    rw [early_on_edge]
    fin_cases i <;> rfl

theorem upper_edge (i : Fin 3) : UniversalTimeTriangle.edgeMap i ≫ OrderedDoubleCutTriangle.upper =
    ![side 2, diagonal, side 3] i := by
  apply TopCat.ext
  intro t
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change ((OrderedDoubleCutTriangle.early (UniversalTimeTriangle.edgeMap i t)).down : ℝ) = _
    rw [early_on_edge]
    fin_cases i <;> rfl
  · apply ULift.ext
    apply Subtype.ext
    change ((OrderedDoubleCutTriangle.late (UniversalTimeTriangle.edgeMap i t)).down : ℝ) = _
    rw [late_on_edge]
    fin_cases i <;> rfl

def sideChain (i : Fin 4) : coeff ⟶ (chains OrderedDoubleCutTimes.square).X 1 :=
  (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (push (side i)).f 1

theorem square_boundary :
    OrderedDoubleCutSquareShuffle.squareChain ≫ (chains OrderedDoubleCutTimes.square).d 2 1 =
      ∑ i : Fin 4, sideChain i := by
  have hc (a : UniversalTimeTriangle.space ⟶ OrderedDoubleCutTimes.square) :
      ((TopCat.toSSet.obj UniversalTimeTriangle.space).ιChainComplex UniversalTimeTriangle.simplex ≫
        (push a).f 2) ≫ (chains OrderedDoubleCutTimes.square).d 2 1 =
      ∑ i : Fin 3, (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫
        (push (UniversalTimeTriangle.edgeMap i ≫ a)).f 1 := by
    rw [Category.assoc, (push a).comm, ← Category.assoc, UniversalTimeTriangle.chain_boundary]
    simp only [Fin.sum_univ_three, push_comp, HomologicalComplex.comp_f,
      Preadditive.add_comp, Category.assoc]
  rw [OrderedDoubleCutSquareShuffle.square_split, Preadditive.add_comp, hc, hc]
  simp only [lower_edge, upper_edge, Fin.sum_univ_three, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sideChain]
  let D := (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (push diagonal).f 1
  have h : D + D = 0 := BorelCochain.two_eq_zero_of_mod D
  calc
    _ = ((TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (push (side 0)).f 1 +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (push (side 1)).f 1 +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (push (side 2)).f 1 +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (push (side 3)).f 1) +
      (D + D) := by dsimp only [D]; abel
    _ = _ := by rw [h, add_zero]

abbrev space := TopCat.of OrderedDoubleCutTimes.boundary

def inclusion : space ⟶ OrderedDoubleCutTimes.square := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem side_mem_boundary (i : Fin 4) (t : TopCat.I.{0}) : side i t ∈ OrderedDoubleCutTimes.boundary := by
  fin_cases i <;> simp [side, OrderedDoubleCutTimes.boundary]

def liftedSide (i : Fin 4) : TopCat.I.{0} ⟶ space := TopCat.ofHom
  ⟨fun t => ⟨side i t, side_mem_boundary i t⟩, (side i).hom.continuous.subtype_mk _⟩

theorem lifted_side (i : Fin 4) : liftedSide i ≫ inclusion = side i := rfl

def boundaryChain : coeff ⟶ (chains space).X 1 :=
  ∑ i : Fin 4, (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫
    (push (liftedSide i)).f 1

theorem boundary_lift : boundaryChain ≫ (push inclusion).f 1 =
    OrderedDoubleCutSquareShuffle.squareChain ≫ (chains OrderedDoubleCutTimes.square).d 2 1 := by
  rw [square_boundary]
  simp only [boundaryChain, sideChain, Preadditive.sum_comp, Category.assoc,
    ← HomologicalComplex.comp_f, ← push_comp, lifted_side]

end
end Finsler.OrderedSquareBoundary
