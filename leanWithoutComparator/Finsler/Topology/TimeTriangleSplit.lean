module

public import Finsler.Topology.IntervalTriangle
public import Finsler.Topology.SingularRightNaturality

/-! The concrete singular triangle splits the actual shuffle time interval
on genuine source cycles. No filtered carrier assertion is included here. -/

@[expose] public section
namespace Finsler.TimeTriangleSplit

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def interval (X : TopCat.{0}) (j : ℕ) :
    (chains X).X j ⟶ (chains (X ⊗ TopCat.I)).X (j + 1) :=
  SingularChainCross.right X TopCat.I j 1 TimeShuffleComparison.intervalSimplex

def triangle (X : TopCat.{0}) (j : ℕ) :
    (chains X).X j ⟶ (chains (X ⊗ TopCat.I)).X (j + 2) :=
  SingularChainCross.right X TopCat.I j 2 IntervalTriangle.triangle

theorem cycle_boundary (X : TopCat.{0}) (j : ℕ) :
    ((chains X).iCycles j ≫ triangle X j) ≫
        (chains (X ⊗ TopCat.I)).d (j + 2) (j + 1) =
      (chains X).iCycles j ≫
        ((interval X j ≫ (SupportedCapNaturality.push (X ◁ IntervalTriangle.secondMap)).f (j + 1)) +
          interval X j +
        (interval X j ≫ (SupportedCapNaturality.push (X ◁ IntervalTriangle.firstMap)).f (j + 1))) := by
  have hb := SingularRightBoundary.rightChain_boundary X TopCat.I j 1
    ((TopCat.toSSet.obj TopCat.I).ιChainComplex IntervalTriangle.triangle)
  have ht : (TopCat.toSSet.obj TopCat.I).ιChainComplex IntervalTriangle.triangle ≫
      (chains TopCat.I).d (1 + 1) 1 =
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫
        (SupportedCapNaturality.push IntervalTriangle.secondMap).f 1 +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫
        (SupportedCapNaturality.push IntervalTriangle.firstMap).f 1 := IntervalTriangle.triangle_boundary
  rw [ht] at hb
  simpa only [SingularRightBoundary.rightChain_simplex,
    SingularRightBoundary.rightChain_add, SingularRightNaturality.rightChain_map_simplex,
    interval, triangle] using hb

end
end Finsler.TimeTriangleSplit
