module

public import Finsler.Loop.OrderedSquareBoundary
public import Finsler.Loop.NormalizedStationaryPrism
public import Finsler.Loop.OrderedDoubleCutClockPrism

/-! The square-boundary prism error from the original shuffle square
is ACTUALLY ZERO on normalized cochains when its homotopy fixes the
four sides. This is applied to BOTH original raw-clock homotopies. -/
@[expose] public section
namespace Finsler.OrderedSquareNormalizedPrism
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

variable {f g : OrderedDoubleCutTimes.square ⟶ OrderedDoubleCutTimes.space}

theorem side_prism_zero (X : TopCat.{0}) (H : TopCat.Homotopy f g)
    (hH : ∀ (v : _root_.unitInterval) (z : OrderedDoubleCutTimes.square),
      z ∈ OrderedDoubleCutTimes.boundary → H (v, z) = f z)
    (i : Fin 4) (q : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (q + 1)) :
    (push (X ◁ OrderedSquareBoundary.side i)).f q ≫ OrderedDoubleCutClockPrism.prism X H q ≫
      SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (q + 1) φ = 0 := by
  apply NormalizedStationaryPrism.stationary_on_subspace
    (OrderedDoubleCutClockPrism.lift X H) (X ◁ OrderedSquareBoundary.side i)
  intro v z
  exact congrArg (fun y => (z.1, y))
    (hH v (OrderedSquareBoundary.side i z.2) (OrderedSquareBoundary.side_mem_boundary i z.2))

theorem square_error_zero (X : TopCat.{0}) (H : TopCat.Homotopy f g)
    (hH : ∀ (v : _root_.unitInterval) (z : OrderedDoubleCutTimes.square),
      z ∈ OrderedDoubleCutTimes.boundary → H (v, z) = f z)
    (p : ℕ) (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3)) :
    OrderedDoubleCutClockPrism.squareError X H p
      (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) = 0 := by
  unfold OrderedDoubleCutClockPrism.squareError
  rw [OrderedSquareBoundary.square_boundary, Fin.sum_univ_four]
  simp only [SingularRightBoundary.rightChain_add, OrderedSquareBoundary.sideChain,
    SingularRightNaturality.rightChain_map_simplex, Preadditive.add_comp, Category.assoc,
    side_prism_zero X H hH, comp_zero, add_zero]

theorem left_square_error_zero (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3)) :
    OrderedDoubleCutClockPrism.squareError X OrderedDoubleCutTimes.leftHomotopy p
      (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) = 0 :=
  square_error_zero X OrderedDoubleCutTimes.leftHomotopy OrderedDoubleCutTimes.left_boundary_fixed p φ

theorem right_square_error_zero (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3)) :
    OrderedDoubleCutClockPrism.squareError X OrderedDoubleCutTimes.rightHomotopy p
      (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) = 0 :=
  square_error_zero X OrderedDoubleCutTimes.rightHomotopy OrderedDoubleCutTimes.right_boundary_fixed p φ

end
end Finsler.OrderedSquareNormalizedPrism
