module

public import Finsler.Loop.NativeSequentialTimeFaces
public import Finsler.Loop.OrderedSquareBoundary
public import Finsler.Loop.OrderedDoubleCutSquareChain

/-! Reassociate the genuine canonical shuffle square into the ORIGINAL
sequential source. Handle its four face chains separately, retaining the
source boundary. No literal cochain zero on the union of closed faces is
inferred from separate face restrictions. -/
@[expose] public section
namespace Finsler.NativeRawTimeSquareBoundary
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

def face (n : ℕ) (i : Fin 4) : Set (source n) :=
  ![innerFace n 0, outerFace n 1, innerFace n 1, outerFace n 0] i

def squareMap (n : ℕ) : Loops n ⊗ OrderedDoubleCutTimes.square ⟶ source n := TopCat.ofHom
  ⟨fun z => ((z.2.1.down, z.1), z.2.2.down), by fun_prop⟩

def sideMap (n : ℕ) (i : Fin 4) : Loops n ⊗ TopCat.I.{0} ⟶ source n :=
  (Loops n ◁ OrderedSquareBoundary.side i) ≫ squareMap n

theorem side_mem_face (n : ℕ) (i : Fin 4) (z : Loops n ⊗ TopCat.I.{0}) :
    sideMap n i z ∈ face n i := by
  fin_cases i <;> rfl

theorem side_zero (n q : ℕ) (T : singularCochainGroup (ZMod 2) (source n) q)
    (hT : ∀ i : Fin 4, cochainPullback (SupportedCap.subspaceMap (source n) (face n i)) q T = 0)
    (i : Fin 4) : cochainPullback (sideMap n i) q T = 0 :=
  NativeSupportedStageCarrier.map_zero (sideMap n i) (face n i) (side_mem_face n i) q T (hT i)

theorem side_chain_zero (n p : ℕ) (T : singularCochainGroup (ZMod 2) (source n) (p + 1))
    (hT : ∀ i : Fin 4, cochainPullback (SupportedCap.subspaceMap (source n) (face n i)) (p + 1) T = 0)
    (i : Fin 4) :
    SingularRightBoundary.rightChain (Loops n) OrderedDoubleCutTimes.square p 1 (OrderedSquareBoundary.sideChain i) ≫
      (push (squareMap n)).f (p + 1) ≫ T = 0 := by
  rw [OrderedSquareBoundary.sideChain, SingularRightNaturality.rightChain_map_simplex]
  simp only [Category.assoc]
  have hz : (push (Loops n ◁ OrderedSquareBoundary.side i)).f (p + 1) ≫
      (push (squareMap n)).f (p + 1) ≫ T = 0 := by
    change cochainPullback (Loops n ◁ OrderedSquareBoundary.side i) (p + 1)
      (cochainPullback (squareMap n) (p + 1) T) = 0
    rw [← pullback_comp]
    exact side_zero n (p + 1) T hT i
  rw [hz, comp_zero]

theorem square_boundary_zero (n p : ℕ) (T : singularCochainGroup (ZMod 2) (source n) (p + 1))
    (hT : ∀ i : Fin 4, cochainPullback (SupportedCap.subspaceMap (source n) (face n i)) (p + 1) T = 0) :
    SingularRightBoundary.rightChain (Loops n) OrderedDoubleCutTimes.square p 1
      (OrderedDoubleCutSquareShuffle.squareChain ≫ (chains OrderedDoubleCutTimes.square).d 2 1) ≫
        (push (squareMap n)).f (p + 1) ≫ T = 0 := by
  rw [OrderedSquareBoundary.square_boundary, Fin.sum_univ_four]
  simp only [SingularRightBoundary.rightChain_add, Preadditive.add_comp,
    side_chain_zero n p T hT, add_zero]

theorem full_boundary_evaluation (n p : ℕ) (T : singularCochainGroup (ZMod 2) (source n) (p + 2))
    (hT : ∀ i : Fin 4, cochainPullback (SupportedCap.subspaceMap (source n) (face n i)) (p + 2) T = 0) :
    OrderedDoubleCutSquareChain.insertion (Loops n) (p + 1) ≫ (push (squareMap n)).f (p + 3) ≫
      (chains (source n)).d (p + 3) (p + 2) ≫ T =
    (chains (Loops n)).d (p + 1) p ≫ OrderedDoubleCutSquareChain.insertion (Loops n) p ≫
      (push (squareMap n)).f (p + 2) ≫ T := by
  rw [← Category.assoc ((push (squareMap n)).f (p + 3)), (push (squareMap n)).comm]
  simp only [Category.assoc]
  rw [← Category.assoc (OrderedDoubleCutSquareChain.insertion (Loops n) (p + 1)),
    OrderedDoubleCutSquareChain.full_boundary, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [square_boundary_zero n (p + 1) T hT, add_zero]

theorem cycle_boundary_zero (n p : ℕ) (T : singularCochainGroup (ZMod 2) (source n) (p + 2))
    (hT : ∀ i : Fin 4, cochainPullback (SupportedCap.subspaceMap (source n) (face n i)) (p + 2) T = 0)
    (c : coeff ⟶ (chains (Loops n)).X (p + 1))
    (hc : c ≫ (chains (Loops n)).d (p + 1) p = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops n) (p + 1) ≫ (push (squareMap n)).f (p + 3) ≫
      (chains (source n)).d (p + 3) (p + 2) ≫ T = 0 := by
  rw [full_boundary_evaluation n p T hT, ← Category.assoc c, hc, zero_comp]

end
end Finsler.NativeRawTimeSquareBoundary
