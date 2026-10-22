module

public import Finsler.Loop.TripleCrossClosedSweep
public import Finsler.Loop.CupAtDegreeCrossPairing

/-! Pair three factorwise cohomology classes with the ORIGINAL
left-associated triple singular cross, by two actual cross/cup
pairing formulas. No homology-cross reassociation is assumed. -/
@[expose] public section
namespace Finsler.TripleCupCrossPairing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def firstProjection (X Y Z : TopCat.{0}) : (X ⊗ Y) ⊗ Z ⟶ X := fst (X ⊗ Y) Z ≫ fst X Y
def secondProjection (X Y Z : TopCat.{0}) : (X ⊗ Y) ⊗ Z ⟶ Y := fst (X ⊗ Y) Z ≫ snd X Y
def thirdProjection (X Y Z : TopCat.{0}) : (X ⊗ Y) ⊗ Z ⟶ Z := snd (X ⊗ Y) Z

def pairClass (X Y : TopCat.{0}) (p q u : ℕ) (hu : p + q = u)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q) :=
  CupAtDegree.cup (X ⊗ Y) p q u hu ((cohPullback (fst X Y) p).hom a) ((cohPullback (snd X Y) q).hom b)

def tripleClass (X Y Z : TopCat.{0}) (p q r u N : ℕ) (hu : p + q = u) (hN : u + r = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q) (c : cohomologyZMod2 Z r) :=
  CupAtDegree.cup ((X ⊗ Y) ⊗ Z) u r N hN
    ((cohPullback (fst (X ⊗ Y) Z) u).hom (pairClass X Y p q u hu a b))
    ((cohPullback (snd (X ⊗ Y) Z) r).hom c)

theorem expanded (X Y Z : TopCat.{0}) (p q r u N : ℕ) (hu : p + q = u) (hN : u + r = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q) (c : cohomologyZMod2 Z r) :
    tripleClass X Y Z p q r u N hu hN a b c =
      CupAtDegree.cup ((X ⊗ Y) ⊗ Z) u r N hN
        (CupAtDegree.cup ((X ⊗ Y) ⊗ Z) p q u hu
          ((cohPullback (firstProjection X Y Z) p).hom a)
          ((cohPullback (secondProjection X Y Z) q).hom b))
        ((cohPullback (thirdProjection X Y Z) r).hom c) := by
  unfold tripleClass pairClass firstProjection secondProjection thirdProjection
  rw [CupAtDegree.naturality, ← Cup.pullback_comp, ← Cup.pullback_comp]

theorem pair_pairing (X Y : TopCat.{0}) (p q u : ℕ) (hu : p + q = u)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q)
    (x : homologyZMod2 X p) (y : homologyZMod2 Y q) :
    (kroneckerMap (X ⊗ Y) u).hom (pairClass X Y p q u hu a b)
      (FilteredBilinearLoopProduct.cross X Y p q u hu x y) =
      (kroneckerMap X p).hom a x * (kroneckerMap Y q).hom b y :=
  CupAtDegreeCrossPairing.cross_cup_apply X Y p q u hu a b x y

theorem triple_pairing (X Y Z : TopCat.{0}) (p q r u N : ℕ) (hu : p + q = u) (hN : u + r = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q) (c : cohomologyZMod2 Z r)
    (x : homologyZMod2 X p) (y : homologyZMod2 Y q) (z : homologyZMod2 Z r) :
    (kroneckerMap ((X ⊗ Y) ⊗ Z) N).hom (tripleClass X Y Z p q r u N hu hN a b c)
      (TripleCrossClosedSweep.tripleCross X Y Z p q r u N hu hN x y z) =
      ((kroneckerMap X p).hom a x * (kroneckerMap Y q).hom b y) * (kroneckerMap Z r).hom c z := by
  have h := CupAtDegreeCrossPairing.cross_cup_apply (X ⊗ Y) Z u r N hN
    (pairClass X Y p q u hu a b) c (FilteredBilinearLoopProduct.cross X Y p q u hu x y) z
  rw [pair_pairing] at h
  exact h

end
end Finsler.TripleCupCrossPairing
