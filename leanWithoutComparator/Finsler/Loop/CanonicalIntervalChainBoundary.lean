module

public import Finsler.Topology.IntervalTriangle
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-! The exact two endpoints of the SAME canonical singular interval.
Its actual chain boundary factors through two actual point inclusions. -/
@[expose] public section
namespace Finsler.CanonicalIntervalChainBoundary
open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

abbrev point := TopCat.of PUnit

def endpoint (t : _root_.unitInterval) : point ⟶ TopCat.I.{0} :=
  TopCat.ofHom ⟨fun _ => ULift.up t, continuous_const⟩

def pointChain : coeff ⟶ (chains point).X 0 :=
  (TopCat.toSSet.obj point).ιChainComplex (TopCat.toSSetObj₀Equiv.symm PUnit.unit)

def intervalChain : coeff ⟶ (chains TopCat.I.{0}).X 1 :=
  (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex

theorem face_zero : (TopCat.toSSet.obj TopCat.I).δ (0 : Fin 2) TimeShuffleComparison.intervalSimplex =
    TopCat.toSSetObj₀Equiv.symm (1 : TopCat.I.{0}) := by
  rw [TimeShuffleComparison.intervalSimplex, ← SSet.stdSimplex.yonedaEquiv_δ_comp,
    SSet.stdSimplex.δ_zero_toSSetObjI]
  exact SSet.yonedaEquiv_const _

theorem face_one : (TopCat.toSSet.obj TopCat.I).δ (1 : Fin 2) TimeShuffleComparison.intervalSimplex =
    TopCat.toSSetObj₀Equiv.symm (0 : TopCat.I.{0}) := by
  rw [TimeShuffleComparison.intervalSimplex, ← SSet.stdSimplex.yonedaEquiv_δ_comp,
    SSet.stdSimplex.δ_one_toSSetObjI]
  exact SSet.yonedaEquiv_const _

theorem endpoint_chain (t : _root_.unitInterval) : pointChain ≫ (push (endpoint t)).f 0 =
    (TopCat.toSSet.obj TopCat.I).ιChainComplex (TopCat.toSSetObj₀Equiv.symm (ULift.up t)) := by
  rw [pointChain, push, SSet.ι_chainComplexMap_f, TauCeti.TopCat.toSSet_map_app_toSSetObj₀Equiv_symm]
  rfl

theorem boundary : intervalChain ≫ (chains TopCat.I.{0}).d 1 0 =
    pointChain ≫ (push (endpoint 1)).f 0 - pointChain ≫ (push (endpoint 0)).f 0 := by
  rw [intervalChain, SSet.ιChainComplex_d, Fin.sum_univ_two, endpoint_chain, endpoint_chain]
  norm_num [face_zero, face_one, sub_eq_add_neg]
  rfl

end
end Finsler.CanonicalIntervalChainBoundary
