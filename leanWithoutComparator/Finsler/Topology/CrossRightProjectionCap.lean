module

public import Finsler.Topology.CrossProjectionCap
public import Finsler.Topology.CrossProjectionZero
public import Finsler.Topology.CupCommutativity

/-! Recover the first factor after capping by the sphere class in the second factor.
Use actual cup-cap duality and F2 cup commutativity, without a new Kunneth theorem. -/

@[expose] public section

namespace Finsler.CrossRightProjectionCap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicTopology SphereOddDegree Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.SphereTopClass Finsler.SphereUnitCandidate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem cup_cap_at (X : TopCat.{0}) (p q m : ℕ) (h : p + q = m)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) (x : PoolCap.homology X m) :
    (kroneckerMap X m).hom (CupUnit.absoluteCast X h (cupZMod2 a b)) x =
      (kroneckerMap X q).hom b (PoolCap.cap X p q m h a x) := by
  subst m
  exact AbsoluteCapEvaluation.cup_cap X p q a b x

theorem projection_cap (X Y : TopCat.{0}) (p q m : ℕ) (h : p + q = m)
    (a : cohomologyZMod2 Y q) (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (PoolCap.push (fst X Y) p).hom
      (PoolCap.cap (X ⊗ Y) q p m (by omega) ((cohPullback (snd X Y) q).hom a)
        (FilteredBilinearLoopProduct.cross X Y p q m h x y)) =
      ((kroneckerMap Y q).hom a y) • x := by
  subst m
  apply KroneckerHomologyExt.homology_ext X p
  intro b
  let z := FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y
  let a' := (cohPullback (snd X Y) q).hom a
  let b' := (cohPullback (fst X Y) p).hom b
  have hc := cup_cap_at (X ⊗ Y) q p (p + q) (Nat.add_comm q p) a' b' z
  rw [CupCommutativity.comm (X ⊗ Y) p q b' a'] at hc
  calc
    _ = (kroneckerMap (X ⊗ Y) p).hom b'
        (PoolCap.cap (X ⊗ Y) q p (p + q) (Nat.add_comm q p) a' z) :=
      (congrArg (fun f => f (PoolCap.cap (X ⊗ Y) q p (p + q)
        (Nat.add_comm q p) a' z)) (kroneckerMap_naturality_apply (fst X Y) p b)).symm
    _ = (kroneckerMap (X ⊗ Y) (p + q)).hom (cupZMod2 b' a') z := hc.symm
    _ = (kroneckerMap X p).hom b x * (kroneckerMap Y q).hom a y :=
      CrossCupPairing.cross_cup_apply X Y p q b a x y
    _ = _ := by rw [map_smul, smul_eq_mul, mul_comm]

theorem sphere_projection_cap (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) (k : ℕ)
    (x : PoolCap.homology X k) :
    (PoolCap.push (fst X (sphere n)) k).hom
      (PoolCap.cap (X ⊗ sphere n) n k (n + k) rfl
        ((cohPullback (snd X (sphere n)) n).hom (topClass n hn))
        (FilteredBilinearLoopProduct.cross X (sphere n) k n (n + k) (Nat.add_comm k n)
          x (fundamental n hn))) = x := by
  rw [projection_cap, top_evaluation_one, one_smul]

theorem projection_zero (X Y : TopCat.{0}) (p q m : ℕ) (h : p + q = m) (hq : q ≠ 0)
    (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (PoolCap.push (fst X Y) m).hom
      (FilteredBilinearLoopProduct.cross X Y p q m h x y) = 0 := by
  let pt : TopCat.{0} := TopCat.of PUnit
  let f : Y ⟶ pt := TopCat.ofHom (ContinuousMap.const Y PUnit.unit)
  have hz : IsZero (PoolCap.homology pt q) :=
    TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace coeff pt hq
  letI : Subsingleton (PoolCap.homology pt q) := ModuleCat.isZero_iff_subsingleton.mp hz
  have hzero : (PoolCap.push f q).hom y = 0 := Subsingleton.elim _ _
  have hproj : (𝟙 X ⊗ₘ f) ≫ fst X pt = fst X Y := by ext z : 1; rfl
  have hmap : PoolCap.push (fst X Y) m =
      PoolCap.push (𝟙 X ⊗ₘ f) m ≫ PoolCap.push (fst X pt) m :=
    (congrArg (fun t => PoolCap.push t m) hproj).symm.trans
      (((singularHomologyFunctor (ModuleCat (ZMod 2)) m).obj coeff).map_comp _ _)
  calc
    _ = (PoolCap.push (fst X pt) m).hom
        ((PoolCap.push (𝟙 X ⊗ₘ f) m).hom (FilteredBilinearLoopProduct.cross X Y p q m h x y)) :=
      ConcreteCategory.congr_hom hmap _
    _ = (PoolCap.push (fst X pt) m).hom
        (FilteredBilinearLoopProduct.cross X pt p q m h
          ((PoolCap.push (𝟙 X) p).hom x) ((PoolCap.push f q).hom y)) :=
      congrArg (PoolCap.push (fst X pt) m).hom
        (CrossProjectionZero.cross_naturality_apply (𝟙 X) f p q m h x y).symm
    _ = 0 := by rw [hzero, map_zero, map_zero]

theorem projection_cap_zero (X Y : TopCat.{0}) (p q m : ℕ) (h : p + q = m) (hq : q ≠ 0)
    (a : cohomologyZMod2 X q) (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (PoolCap.push (fst X Y) p).hom
      (PoolCap.cap (X ⊗ Y) q p m (by omega) ((cohPullback (fst X Y) q).hom a)
        (FilteredBilinearLoopProduct.cross X Y p q m h x y)) = 0 := by
  rw [PoolCap.naturality, projection_zero X Y p q m h hq x y, map_zero]

end
end Finsler.CrossRightProjectionCap

