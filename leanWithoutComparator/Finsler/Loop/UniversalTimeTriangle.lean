module

public import Finsler.Topology.IntervalTriangle

/-! The ACTUAL universal singular2-simplex with all THREE real edges,
parameterized by the SAME canonical interval simplex used in the
original time prism. Moving clock maps will be postcomposed with this
triangle, so their intermediate time may depend on the source. -/
@[expose] public section
namespace Finsler.UniversalTimeTriangle
open CategoryTheory AlgebraicTopology Convexity
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev space : TopCat.{0} := TopCat.of (StdSimplex ℝ (Fin 3))
def simplexMap : C(StdSimplex ℝ (Fin 3), space) :=
  (ContinuousMap.id _).comp (StdSimplex.continuousAffineMapMk (fun i : Fin 3 => StdSimplex.single i))
def simplex : TopCat.toSSet.obj space _⦋2⦌ := (space.toSSetObjEquiv _).symm simplexMap

def edgeMap (i : Fin 3) : TopCat.I.{0} ⟶ space :=
  TopCat.ofHom ((StdSimplex.continuousAffineMapMk (fun j : Fin 2 => StdSimplex.single (R := ℝ) (i.succAbove j))).comp
    ⟨TopCat.stdSimplexHomeomorphI.symm, TopCat.stdSimplexHomeomorphI.symm.continuous⟩)

theorem face (i : Fin 3) :
    (TopCat.toSSet.obj space).δ i simplex = (TopCat.toSSet.map (edgeMap i)).app _ TimeShuffleComparison.intervalSimplex := by
  rw [simplex, simplexMap, TauCeti.TopCat.δ_toSSetObjEquiv_symm_comp_affineMapMk,
    IntervalTriangle.canonical_simplex, TauCeti.TopCat.toSSet_map_app_toSSetObjEquiv_symm]
  apply (space.toSSetObjEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro x
  have h := congrArg (fun y : StdSimplex ℝ (Fin 2) =>
    (StdSimplex.continuousAffineMapMk (fun j : Fin 2 => StdSimplex.single (R := ℝ) (i.succAbove j))) y)
    (TopCat.stdSimplexHomeomorphI.symm_apply_apply x)
  simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply, edgeMap, IntervalTriangle.intervalMap,
    TopCat.hom_ofHom, TopCat.ofHom_apply, ContinuousMap.coe_mk, Function.comp_def] using h.symm

theorem interval_inverse_weight_one (t : TopCat.I.{0}) :
    (TopCat.stdSimplexHomeomorphI.symm t).weights 1 = (t.down : ℝ) := by
  calc
    _ = ((IntervalTriangle.intervalMap (TopCat.stdSimplexHomeomorphI.symm t)).down : ℝ) :=
      (IntervalTriangle.interval_coordinate _).symm
    _ = _ := congrArg (fun u : TopCat.I.{0} => (u.down : ℝ)) (TopCat.stdSimplexHomeomorphI.apply_symm_apply t)

theorem interval_inverse_weight_zero (t : TopCat.I.{0}) :
    (TopCat.stdSimplexHomeomorphI.symm t).weights 0 = 1 - (t.down : ℝ) := by
  have ht := (TopCat.stdSimplexHomeomorphI.symm t).total_of_fintype
  rw [Fin.sum_univ_two, interval_inverse_weight_one] at ht
  linarith

private theorem neg_self (f : coeff ⟶ (chains space).X 1) : -f = f := by
  have h := BorelCochain.two_eq_zero_of_mod f
  calc
    -f = -f + (f + f) := by rw [h, add_zero]
    _ = f := by abel

theorem chain_boundary :
    (TopCat.toSSet.obj space).ιChainComplex simplex ≫ (chains space).d 2 1 =
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (SupportedCapNaturality.push (edgeMap 0)).f 1 +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (SupportedCapNaturality.push (edgeMap 1)).f 1 +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫ (SupportedCapNaturality.push (edgeMap 2)).f 1 := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_three]
  norm_num [face, neg_self, SupportedCapNaturality.push, SSet.ι_chainComplexMap_f]

end
end Finsler.UniversalTimeTriangle
