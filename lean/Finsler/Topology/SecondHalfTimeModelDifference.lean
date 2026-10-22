module

public import Finsler.Topology.FullTensorTimePrism
public import Finsler.Topology.OriginalSecondHalfTensorTimeOperation
public import Finsler.Topology.TimePrismComparison
import all Finsler.Topology.OriginalSecondHalfTimeOperation

/-! The two actual second-half time models have literally the same
endpoint maps. Their difference is therefore closed on every actual
input cycle, including input degree zero. This is the concrete cycle
to be filled by the standard-model acyclic construction. It is not yet
a proof that the two capped homology operations agree. -/

@[expose] public section
namespace Finsler.SecondHalfTimeModelDifference

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]

def productPrism : Homotopy
    (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q) ≫
      push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 0))
    (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q) ≫
      push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 1)) :=
  (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).compLeft
    (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))

def tensorPrism : Homotopy
    (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q) ≫
      push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 0))
    (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q) ≫
      push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 1)) := by
  have H := (FullTensorTimePrism.prism (TopCat.of P) (TopCat.of Q)).compRight
    (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of (ClosedInterval × Q)))
  simpa only [OriginalSecondHalfTensorTimeOperation.slice_cross] using H

def difference (N : ℕ) :
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q)).X N ⟶
      (chains (TopCat.of (P × (ClosedInterval × Q)))).X (N + 1) :=
  (productPrism (P := P) (Q := Q)).hom N (N + 1) -
    (tensorPrism (P := P) (Q := Q)).hom N (N + 1)

private theorem homotopy_boundary {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : C ⟶ D} (H : Homotopy f₀ f₁) (N : ℕ) :
    C.d (N + 1) N ≫ H.hom N (N + 1) + H.hom (N + 1) (N + 2) ≫ D.d (N + 2) (N + 1) =
      f₀.f (N + 1) - f₁.f (N + 1) := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
    (H.comm (N + 1)).symm

theorem comm (N : ℕ) :
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q)).d (N + 1) N ≫ difference (P := P) (Q := Q) N +
      difference (P := P) (Q := Q) (N + 1) ≫
        (chains (TopCat.of (P × (ClosedInterval × Q)))).d (N + 2) (N + 1) = 0 := by
  calc
    _ = ((chains (TopCat.of P) ⊗ chains (TopCat.of Q)).d (N + 1) N ≫
        (productPrism (P := P) (Q := Q)).hom N (N + 1) +
        (productPrism (P := P) (Q := Q)).hom (N + 1) (N + 2) ≫
          (chains (TopCat.of (P × (ClosedInterval × Q)))).d (N + 2) (N + 1)) -
      ((chains (TopCat.of P) ⊗ chains (TopCat.of Q)).d (N + 1) N ≫
        (tensorPrism (P := P) (Q := Q)).hom N (N + 1) +
        (tensorPrism (P := P) (Q := Q)).hom (N + 1) (N + 2) ≫
          (chains (TopCat.of (P × (ClosedInterval × Q)))).d (N + 2) (N + 1)) := by
      simp only [difference, Preadditive.comp_sub, Preadditive.sub_comp]
      abel
    _ = 0 := by rw [homotopy_boundary, homotopy_boundary, sub_self]

theorem cycles_closed (N : ℕ) :
    ((chains (TopCat.of P) ⊗ chains (TopCat.of Q)).iCycles N ≫ difference (P := P) (Q := Q) N) ≫
      (chains (TopCat.of (P × (ClosedInterval × Q)))).d (N + 1) N = 0 := by
  simp only [difference, Preadditive.comp_sub, Preadditive.sub_comp]
  rw [TimePrismComparison.cycles_prism_boundary, TimePrismComparison.cycles_prism_boundary, sub_self]

def cycles (N : ℕ) :
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q)).cycles N ⟶
      (chains (TopCat.of (P × (ClosedInterval × Q)))).cycles (N + 1) :=
  (chains (TopCat.of (P × (ClosedInterval × Q)))).liftCycles
    ((chains (TopCat.of P) ⊗ chains (TopCat.of Q)).iCycles N ≫ difference (P := P) (Q := Q) N)
    N (by simp [ChainComplex.next_nat_succ]) (cycles_closed N)

theorem cycles_i (N : ℕ) :
    cycles (P := P) (Q := Q) N ≫
      (chains (TopCat.of (P × (ClosedInterval × Q)))).iCycles (N + 1) =
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q)).iCycles N ≫ difference (P := P) (Q := Q) N :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

end
end Finsler.SecondHalfTimeModelDifference
