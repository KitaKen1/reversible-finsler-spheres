module

public import Finsler.Loop.ClosedSecondFactorSweepCross

/-! Sweep an arbitrary one of THREE factors while preserving the
original LEFT-associated genuine homology cross. This deliberately
does not reassociate the singular cross product. It will compute
the actual ordered-cell inputs directly in their original factors. -/
@[expose] public section
namespace Finsler.TripleCrossClosedSweep
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def tripleCross (X Y Z : TopCat.{0}) (i j k u N : ℕ) (hij : i + j = u) (hu : u + k = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) (z : homologyZMod2 Z k) :=
  FilteredBilinearLoopProduct.cross (X ⊗ Y) Z u k N hu
    (FilteredBilinearLoopProduct.cross X Y i j u hij x y) z

def first {X X' : TopCat.{0}} {f : X ⟶ X'} (H : TopCat.Homotopy f f) (Y Z : TopCat.{0}) :=
  ClosedFirstFactorSweepCross.productHomotopy (ClosedFirstFactorSweepCross.productHomotopy H Y) Z

def second (X : TopCat.{0}) {Y Y' : TopCat.{0}} {g : Y ⟶ Y'} (H : TopCat.Homotopy g g) (Z : TopCat.{0}) :=
  ClosedFirstFactorSweepCross.productHomotopy (ClosedSecondFactorSweepCross.productHomotopy X H) Z

def third (X Y : TopCat.{0}) {Z Z' : TopCat.{0}} {h : Z ⟶ Z'} (H : TopCat.Homotopy h h) :=
  ClosedSecondFactorSweepCross.productHomotopy (X ⊗ Y) H

theorem first_value {X X' : TopCat.{0}} {f : X ⟶ X'} (H : TopCat.Homotopy f f) (Y Z : TopCat.{0})
    (i j k u N : ℕ) (hij : i + j = u) (hu : u + k = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) (z : homologyZMod2 Z k) :
    (SelfHomotopySweep.homology ((first H Y Z).toSSet.chainComplexMap coeff) N).hom
      (tripleCross X Y Z i j k u N hij hu x y z) =
    tripleCross X' Y Z (i + 1) j k (u + 1) (N + 1) (by omega) (by omega)
      ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) i).hom x) y z := by
  dsimp only [first, tripleCross]
  rw [ClosedFirstFactorSweepCross.cross_value_of_eq, ClosedFirstFactorSweepCross.cross_value_of_eq]

theorem second_value (X : TopCat.{0}) {Y Y' : TopCat.{0}} {g : Y ⟶ Y'} (H : TopCat.Homotopy g g) (Z : TopCat.{0})
    (i j k u N : ℕ) (hij : i + j = u) (hu : u + k = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) (z : homologyZMod2 Z k) :
    (SelfHomotopySweep.homology ((second X H Z).toSSet.chainComplexMap coeff) N).hom
      (tripleCross X Y Z i j k u N hij hu x y z) =
    tripleCross X Y' Z i (j + 1) k (u + 1) (N + 1) (by omega) (by omega)
      x ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) j).hom y) z := by
  dsimp only [second, tripleCross]
  rw [ClosedFirstFactorSweepCross.cross_value_of_eq, ClosedSecondFactorSweepCross.cross_value_of_eq]

theorem third_value (X Y : TopCat.{0}) {Z Z' : TopCat.{0}} {h : Z ⟶ Z'} (H : TopCat.Homotopy h h)
    (i j k u N : ℕ) (hij : i + j = u) (hu : u + k = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) (z : homologyZMod2 Z k) :
    (SelfHomotopySweep.homology ((third X Y H).toSSet.chainComplexMap coeff) N).hom
      (tripleCross X Y Z i j k u N hij hu x y z) =
    tripleCross X Y Z' i j (k + 1) u (N + 1) hij (by omega)
      x y ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) k).hom z) := by
  dsimp only [third, tripleCross]
  rw [ClosedSecondFactorSweepCross.cross_value_of_eq]

theorem first_second_value {X X' Y Y' : TopCat.{0}} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (H : TopCat.Homotopy f f) (K : TopCat.Homotopy g g) (Z : TopCat.{0})
    (i j k u N : ℕ) (hij : i + j = u) (hu : u + k = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) (z : homologyZMod2 Z k) :
    (SelfHomotopySweep.homology ((second X' K Z).toSSet.chainComplexMap coeff) (N + 1)).hom
      ((SelfHomotopySweep.homology ((first H Y Z).toSSet.chainComplexMap coeff) N).hom
        (tripleCross X Y Z i j k u N hij hu x y z)) =
    (SelfHomotopySweep.homology ((first H Y' Z).toSSet.chainComplexMap coeff) (N + 1)).hom
      ((SelfHomotopySweep.homology ((second X K Z).toSSet.chainComplexMap coeff) N).hom
        (tripleCross X Y Z i j k u N hij hu x y z)) := by
  simp only [first_value, second_value]

theorem first_third_value {X X' Z Z' : TopCat.{0}} {f : X ⟶ X'} {h : Z ⟶ Z'}
    (H : TopCat.Homotopy f f) (Y : TopCat.{0}) (K : TopCat.Homotopy h h)
    (i j k u N : ℕ) (hij : i + j = u) (hu : u + k = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) (z : homologyZMod2 Z k) :
    (SelfHomotopySweep.homology ((third X' Y K).toSSet.chainComplexMap coeff) (N + 1)).hom
      ((SelfHomotopySweep.homology ((first H Y Z).toSSet.chainComplexMap coeff) N).hom
        (tripleCross X Y Z i j k u N hij hu x y z)) =
    (SelfHomotopySweep.homology ((first H Y Z').toSSet.chainComplexMap coeff) (N + 1)).hom
      ((SelfHomotopySweep.homology ((third X Y K).toSSet.chainComplexMap coeff) N).hom
        (tripleCross X Y Z i j k u N hij hu x y z)) := by
  simp only [first_value, third_value]

theorem second_third_value {Y Y' Z Z' : TopCat.{0}} {g : Y ⟶ Y'} {h : Z ⟶ Z'}
    (X : TopCat.{0}) (H : TopCat.Homotopy g g) (K : TopCat.Homotopy h h)
    (i j k u N : ℕ) (hij : i + j = u) (hu : u + k = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) (z : homologyZMod2 Z k) :
    (SelfHomotopySweep.homology ((third X Y' K).toSSet.chainComplexMap coeff) (N + 1)).hom
      ((SelfHomotopySweep.homology ((second X H Z).toSSet.chainComplexMap coeff) N).hom
        (tripleCross X Y Z i j k u N hij hu x y z)) =
    (SelfHomotopySweep.homology ((second X H Z').toSSet.chainComplexMap coeff) (N + 1)).hom
      ((SelfHomotopySweep.homology ((third X Y K).toSSet.chainComplexMap coeff) N).hom
        (tripleCross X Y Z i j k u N hij hu x y z)) := by
  simp only [second_value, third_value]

end
end Finsler.TripleCrossClosedSweep
