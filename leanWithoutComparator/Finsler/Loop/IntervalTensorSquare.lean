module

public import Finsler.Loop.RightTensorInsertion
public import Finsler.Loop.CanonicalIntervalChainBoundary
public import Finsler.Loop.TwoTimeSquareCoordinates
public import Finsler.Topology.SmallCrossNaturality
public import Finsler.Loop.OrderedDoubleCutSquareChain

/-! The tensor-time side after inserting the original interval IS the
actual canonical (1,1) shuffle square, after the explicit time-coordinate
swap. No strict three-factor shuffle associativity is assumed. -/
@[expose] public section
namespace Finsler.IntervalTensorSquare
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.IntervalSobolev
open Finsler.CanonicalIntervalChainBoundary Finsler.TwoTimeSquareCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

theorem rightChain_natural (X : TopCat.{0}) {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (p q : ℕ) (c : coeff ⟶ (chains Y).X q) :
    SingularRightBoundary.rightChain X Y p q c ≫ (push (X ◁ f)).f (p + q) =
      SingularRightBoundary.rightChain X Z p q (c ≫ (push f).f q) := by
  have hc := congrArg (fun h => h.f (p + q)) (SmallCrossNaturality.ambient_naturality (𝟙 X) f)
  have hid : push (𝟙 X) = 𝟙 (chains X) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 X)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [HomologicalComplex.comp_f, hid, id_tensorHom] at hc
  rw [← RightTensorInsertion.shuffle, ← RightTensorInsertion.shuffle, Category.assoc]
  change RightTensorInsertion.insert (chains X) (chains Y) p q c ≫
    ((SmallRectangleCross.ambient X Y).f (p + q) ≫ (push (X ◁ f)).f (p + q)) = _
  rw [← hc, ← Category.assoc]
  have hi := RightTensorInsertion.naturality (chains X) (push f) p q c
  rw [id_tensorHom] at hi
  rw [hi]
  rfl

theorem prism_swap (Y : TopCat.{0}) (q : ℕ) : AnnularTimeTrim.prism Y q ≫
    (push (timeSwap Y)).f (q + 1) = TimeTriangleSplit.interval Y q := by
  rw [AnnularTimeTrim.prism, TimePrismNaturality.prism_post, ← RightIntervalCochain.prism]
  exact TimePrismNaturality.prism_congr _ _ rfl q

theorem square_chain : (intervalChain ≫ AnnularTimeTrim.prism TopCat.I 1) ≫
    (push (timeSwap TopCat.I)).f 2 = OrderedDoubleCutSquareShuffle.squareChain := by
  rw [Category.assoc, prism_swap]
  rfl

theorem tensor_insert (X : TopCat.{0}) (p : ℕ) :
    RightTensorInsertion.insert (chains X) (chains TopCat.I) p 1 intervalChain ≫
      (FullTensorTimePrism.prism X TopCat.I).hom (p + 1) (p + 2) =
    RightTensorInsertion.insert (chains X) (chains (TopCat.of (ClosedInterval × TopCat.I))) p 2
      (intervalChain ≫ AnnularTimeTrim.prism TopCat.I 1) := by
  have h := FullTensorTimePrism.on_summand X TopCat.I p 1
  have hs {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (v : V) :
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, 2) • v = v := by
    change ((-1 : ℤˣ) ^ p) • v = v
    simpa only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
      SingularRightFullBoundary.sign_smul p v
  norm_num only [Nat.reduceAdd] at h
  have h' := h.trans (hs _)
  unfold RightTensorInsertion.insert
  simp only [Category.assoc]
  rw [h']
  simp only [id_tensorHom, ← whiskerLeft_comp_assoc]

theorem tensor_square (X : TopCat.{0}) (p : ℕ) :
    RightTensorInsertion.insert (chains X) (chains TopCat.I) p 1 intervalChain ≫
      (FullTensorTimePrism.prism X TopCat.I).hom (p + 1) (p + 2) ≫
        (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × TopCat.I))).f (p + 2) ≫
          (push (X ◁ timeSwap TopCat.I)).f (p + 2) = OrderedDoubleCutSquareChain.insertion X p := by
  rw [← Category.assoc (RightTensorInsertion.insert _ _ p 1 intervalChain), tensor_insert]
  change (RightTensorInsertion.insert (chains X) (chains (TopCat.of (ClosedInterval × TopCat.I))) p 2
    (intervalChain ≫ AnnularTimeTrim.prism TopCat.I 1) ≫ (SingularRightBoundary.shuffle _ _).f (p + 2)) ≫ _ = _
  rw [RightTensorInsertion.shuffle, rightChain_natural, square_chain]
  rfl

end
end Finsler.IntervalTensorSquare
