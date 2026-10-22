module

public import Finsler.Topology.CrossCupPairing
public import Finsler.Topology.KroneckerHomologyExt
public import Finsler.Topology.AbsoluteCapEvaluation
public import Finsler.Topology.SphereUnitCandidate

/-! The sphere-factor cap/projection calculation in the actual models.
An arbitrary homology class of Y is recovered after capping the external
product with the normalized sphere top class and projecting to Y. -/

@[expose] public section

namespace Finsler.CrossProjectionCap

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.BorelEvaluation Finsler.SphereTopClass
open Finsler.SphereUnitCandidate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem projection_cap (X Y : TopCat.{0}) (p q : ℕ)
    (a : cohomologyZMod2 X p) (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (PoolCap.push (snd X Y) q).hom
      (PoolCap.cap (X ⊗ Y) p q (p + q) rfl ((cohPullback (fst X Y) p).hom a)
        (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y)) =
      ((kroneckerMap X p).hom a x) • y := by
  apply KroneckerHomologyExt.homology_ext Y q
  intro b
  calc
    _ = (kroneckerMap (X ⊗ Y) q).hom ((cohPullback (snd X Y) q).hom b)
        (PoolCap.cap (X ⊗ Y) p q (p + q) rfl ((cohPullback (fst X Y) p).hom a)
          (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y)) :=
      (congrArg (fun f => f
        (PoolCap.cap (X ⊗ Y) p q (p + q) rfl ((cohPullback (fst X Y) p).hom a)
          (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y)))
        (kroneckerMap_naturality_apply (snd X Y) q b)).symm
    _ = (kroneckerMap (X ⊗ Y) (p + q)).hom
        (cupZMod2 ((cohPullback (fst X Y) p).hom a) ((cohPullback (snd X Y) q).hom b))
          (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y) :=
      (AbsoluteCapEvaluation.cup_cap (X ⊗ Y) p q _ _ _).symm
    _ = (kroneckerMap X p).hom a x * (kroneckerMap Y q).hom b y :=
      CrossCupPairing.cross_cup_apply X Y p q a b x y
    _ = _ := by rw [map_smul, smul_eq_mul]

theorem sphere_projection_cap (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (k : ℕ)
    (y : PoolCap.homology Y k) :
    (PoolCap.push (snd (sphere n) Y) k).hom
      (PoolCap.cap (sphere n ⊗ Y) n k (n + k) rfl
        ((cohPullback (fst (sphere n) Y) n).hom (topClass n hn))
          (FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl
            (fundamental n hn) y)) = y := by
  rw [projection_cap, top_evaluation_one, one_smul]


end
end Finsler.CrossProjectionCap
