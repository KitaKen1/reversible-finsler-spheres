module

public import Finsler.Topology.DiagonalCocycle
public import Finsler.Topology.DiagonalSymmetry
public import Finsler.Topology.CochainClassExact

/-! A supported primitive for the change of the diagonal cocycle under swap.
This is a cochain correction on the sphere product, not the geometric
cut--join interchange on filtered loop chains. -/

@[expose] public section

namespace Finsler.DiagonalSwapPrimitive

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison
open Finsler.DiagonalCohomology Finsler.DiagonalCocycle Finsler.DiagonalSymmetry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def swappedRelative (n : ℕ) (hn : 1 ≤ n) : RelativeCupCochain.relative (diagonalPair n) n :=
  RelativeCupCochain.pullback (exchangePair n) n (relativeCocycle n hn)

theorem swapped_closed (n : ℕ) (hn : 1 ≤ n) :
    ((RelativeCup.cx (diagonalPair n)).d n (n + 1)).hom (swappedRelative n hn) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (diagonalPair n))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
      (exchangePair n)) n (relativeCocycle n hn) (relative_closed n hn)

theorem swapped_class (n : ℕ) (hn : 2 ≤ n) :
    CochainClass.classOf (RelativeCup.cx (diagonalPair n)) n (swappedRelative n (by omega))
      (swapped_closed n (by omega)) = relativeClass n (by omega) := by
  let f := TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
    (exchangePair n)
  have he := CochainClass.classOf_map (RelativeCup.cx (diagonalPair n)) f n
    (relativeCocycle n (by omega)) (relative_closed n (by omega)) (swapped_closed n (by omega))
  calc
    _ = (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (exchangePair n) n).hom
          (CochainClass.classOf (RelativeCup.cx (diagonalPair n)) n
            (relativeCocycle n (by omega)) (relative_closed n (by omega))) := he.symm
    _ = (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (exchangePair n) n).hom (relativeClass n (by omega)) := by
      rw [relative_cocycle_class]
    _ = relativeClass n (by omega) := relativeClass_exchange n hn

def relativePrimitive (n : ℕ) (hn : 2 ≤ n) :
    RelativeCupCochain.relative (diagonalPair n) (n - 1) :=
  CochainClassExact.primitive (RelativeCup.cx (diagonalPair n)) n (by omega)
    (swappedRelative n (by omega)) (relativeCocycle n (by omega))
    (swapped_closed n (by omega)) (relative_closed n (by omega))
    ((swapped_class n hn).trans (relative_cocycle_class n (by omega)).symm)

theorem relativePrimitive_boundary (n : ℕ) (hn : 2 ≤ n) :
    ((RelativeCup.cx (diagonalPair n)).d (n - 1) n).hom (relativePrimitive n hn) =
      swappedRelative n (by omega) - relativeCocycle n (by omega) :=
  CochainClassExact.primitive_d (RelativeCup.cx (diagonalPair n)) n (by omega)
    (swappedRelative n (by omega)) (relativeCocycle n (by omega))
    (swapped_closed n (by omega)) (relative_closed n (by omega))
    ((swapped_class n hn).trans (relative_cocycle_class n (by omega)).symm)

def ambientPrimitive (n : ℕ) (hn : 2 ≤ n) :
    singularCochainGroup (ZMod 2) (product n) (n - 1) :=
  RelativeCupCochain.toAmbient (diagonalPair n) (n - 1) (relativePrimitive n hn)

theorem ambientPrimitive_supported (n : ℕ) (hn : 2 ≤ n) :
    cochainPullback (diagonalPair n).map (n - 1) (ambientPrimitive n hn) = 0 :=
  RelativeCupCochain.restriction_toAmbient (diagonalPair n) (n - 1) (relativePrimitive n hn)

theorem swapped_toAmbient (n : ℕ) (hn : 1 ≤ n) :
    RelativeCupCochain.toAmbient (diagonalPair n) n (swappedRelative n hn) =
      cochainPullback (exchange n) n (ambientCocycle n hn) := by
  change RelativeCupCochain.toAmbient (diagonalPair n) n
    (RelativeCupCochain.pullback (exchangePair n) n (relativeCocycle n hn)) = _
  rw [RelativeCupCochain.toAmbient_pullback, exchangePair_fst]
  rfl

theorem ambientPrimitive_boundary (n : ℕ) (hn : 2 ≤ n) :
    ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn) =
      cochainPullback (exchange n) n (ambientCocycle n (by omega)) -
        ambientCocycle n (by omega) := by
  have he := ConcreteCategory.congr_hom
    ((RelativeCup.ambientMap (diagonalPair n)).comm (n - 1) n) (relativePrimitive n hn)
  change ((cochainCxZMod2 (product n)).d (n - 1) n).hom (ambientPrimitive n hn) =
    RelativeCupCochain.toAmbient (diagonalPair n) n
      (((RelativeCup.cx (diagonalPair n)).d (n - 1) n).hom (relativePrimitive n hn)) at he
  rw [he, relativePrimitive_boundary, map_sub, swapped_toAmbient]
  rfl


end
end Finsler.DiagonalSwapPrimitive
