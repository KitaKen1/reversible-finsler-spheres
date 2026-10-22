module

public import Finsler.Loop.OrderedDoubleCutSquareShuffle

/-! The actual shuffle square inserted beside an ARBITRARY source.
Both affine folds have the same ordered-triangle term, together with
their two explicit diagonal corrections. The FULL source-boundary
identity is retained; no cycle assumption discards that term. -/
@[expose] public section
namespace Finsler.OrderedDoubleCutSquareChain
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def insertion (X : TopCat.{0}) (p : ℕ) :
    (chains X).X p ⟶ (chains (X ⊗ OrderedDoubleCutTimes.square)).X (p + 2) :=
  SingularRightBoundary.rightChain X OrderedDoubleCutTimes.square p 2
    OrderedDoubleCutSquareShuffle.squareChain

def common (X : TopCat.{0}) (p : ℕ) :=
  UniversalTimeTriangleChain.triangle X p ≫
    (push (X ◁ OrderedDoubleCutTriangle.triangleMap)).f (p + 2)

def diagonalInsertion (X : TopCat.{0}) (a : OrderedDoubleCutTriangle.triangle ⟶ TopCat.I.{0}) (p : ℕ) :=
  UniversalTimeTriangleChain.triangle X p ≫
    (push (X ◁ (a ≫ OrderedDoubleCutTriangle.diagonal))).f (p + 2)

theorem push_whisker_comp (X : TopCat.{0}) {A B C : TopCat.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (k : ℕ) :
    (push (X ◁ f)).f k ≫ (push (X ◁ g)).f k = (push (X ◁ (f ≫ g))).f k := by
  have h := congrArg (fun h => h.f k) (push_comp (X ◁ f) (X ◁ g))
  simpa only [HomologicalComplex.comp_f, whiskerLeft_comp] using h.symm

theorem insertion_split (X : TopCat.{0}) (p : ℕ) : insertion X p =
    UniversalTimeTriangleChain.triangle X p ≫ (push (X ◁ OrderedDoubleCutTriangle.lower)).f (p + 2) +
    UniversalTimeTriangleChain.triangle X p ≫ (push (X ◁ OrderedDoubleCutTriangle.upper)).f (p + 2) := by
  rw [insertion, OrderedDoubleCutSquareShuffle.square_split,
    SingularRightBoundary.rightChain_add,
    SingularRightNaturality.rightChain_map_simplex, SingularRightNaturality.rightChain_map_simplex]
  rfl

theorem left_affine_image (X : TopCat.{0}) (p : ℕ) :
    insertion X p ≫ (push (X ◁ OrderedDoubleCutTimes.leftAffine)).f (p + 2) =
      common X p + diagonalInsertion X OrderedDoubleCutTriangle.early p := by
  rw [insertion_split, Preadditive.add_comp]
  simp only [Category.assoc, push_whisker_comp, OrderedDoubleCutTriangle.lower_left,
    OrderedDoubleCutTriangle.upper_left_diagonal, common, diagonalInsertion]

theorem right_affine_image (X : TopCat.{0}) (p : ℕ) :
    insertion X p ≫ (push (X ◁ OrderedDoubleCutTimes.rightAffine)).f (p + 2) =
      common X p + diagonalInsertion X OrderedDoubleCutTriangle.late p := by
  rw [insertion_split, Preadditive.add_comp]
  simp only [Category.assoc, push_whisker_comp, OrderedDoubleCutTriangle.upper_right,
    OrderedDoubleCutTriangle.lower_right_diagonal, common, diagonalInsertion]
  exact add_comm _ _

theorem affine_difference (X : TopCat.{0}) (p : ℕ) :
    insertion X p ≫ (push (X ◁ OrderedDoubleCutTimes.leftAffine)).f (p + 2) +
      insertion X p ≫ (push (X ◁ OrderedDoubleCutTimes.rightAffine)).f (p + 2) =
    diagonalInsertion X OrderedDoubleCutTriangle.early p +
      diagonalInsertion X OrderedDoubleCutTriangle.late p := by
  rw [left_affine_image, right_affine_image]
  have h := BorelCochain.two_eq_zero_of_mod (common X p)
  calc
    _ = (common X p + common X p) +
        (diagonalInsertion X OrderedDoubleCutTriangle.early p +
          diagonalInsertion X OrderedDoubleCutTriangle.late p) := by abel
    _ = _ := by rw [h, zero_add]

theorem diagonal_zero (X : TopCat.{0}) (p : ℕ)
    (a : OrderedDoubleCutTriangle.triangle ⟶ TopCat.I.{0})
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 2))
    (hφ : cochainPullback (X ◁ OrderedDoubleCutTriangle.diagonal) (p + 2) φ = 0) :
    diagonalInsertion X a p ≫ φ = 0 := by
  unfold diagonalInsertion
  rw [← push_whisker_comp, Category.assoc, Category.assoc]
  change UniversalTimeTriangleChain.triangle X p ≫ (push (X ◁ a)).f (p + 2) ≫
    cochainPullback (X ◁ OrderedDoubleCutTriangle.diagonal) (p + 2) φ = 0
  rw [hφ, comp_zero, comp_zero]

theorem affine_cochain_comparison (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 2))
    (hφ : cochainPullback (X ◁ OrderedDoubleCutTriangle.diagonal) (p + 2) φ = 0) :
    insertion X p ≫ cochainPullback (X ◁ OrderedDoubleCutTimes.leftAffine) (p + 2) φ =
      insertion X p ≫ cochainPullback (X ◁ OrderedDoubleCutTimes.rightAffine) (p + 2) φ := by
  change (insertion X p ≫ (push (X ◁ OrderedDoubleCutTimes.leftAffine)).f (p + 2)) ≫ φ =
    (insertion X p ≫ (push (X ◁ OrderedDoubleCutTimes.rightAffine)).f (p + 2)) ≫ φ
  rw [left_affine_image, right_affine_image, Preadditive.add_comp, Preadditive.add_comp,
    diagonal_zero X p OrderedDoubleCutTriangle.early φ hφ,
    diagonal_zero X p OrderedDoubleCutTriangle.late φ hφ]

theorem full_boundary (X : TopCat.{0}) (p : ℕ) :
    insertion X (p + 1) ≫ (chains (X ⊗ OrderedDoubleCutTimes.square)).d (p + 3) (p + 2) =
    (chains X).d (p + 1) p ≫ insertion X p +
      SingularRightBoundary.rightChain X OrderedDoubleCutTimes.square (p + 1) 1
        (OrderedDoubleCutSquareShuffle.squareChain ≫ (chains OrderedDoubleCutTimes.square).d 2 1) :=
  SingularRightFullBoundary.rightChain_boundary_two X OrderedDoubleCutTimes.square p
    OrderedDoubleCutSquareShuffle.squareChain

end
end Finsler.OrderedDoubleCutSquareChain
