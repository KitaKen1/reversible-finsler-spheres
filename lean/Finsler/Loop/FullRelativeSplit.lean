module

public import Finsler.Loop.ConstantSublevelRetract
public import Finsler.Loop.ConstantRelativePairing

/-! The ORIGINAL full H1-loop pair has an actual linear relative
lift in all degrees. On the kernel of restriction to constants it
is the unique genuine lift. This removes adjacent-degree vanishing
from existence/uniqueness and the real relative Kronecker pairing. -/

@[expose] public section
namespace Finsler.FullRelativeSplit
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def lift (n k : ℕ) : cohomologyZMod2 (Loops n) k →ₗ[ZMod 2]
    RelativeCup.cohomology (fullPair n) k :=
  (RetractedPairCohomology.lift (fullPair n)
    (ConstantSublevelRetract.retraction Set.univ (Set.subset_univ _))
    (ConstantSublevelRetract.left_inverse Set.univ (Set.subset_univ _)) k).comp
      (FullLoopModel.cohomologyEquiv n k).toLinearMap

def absolute (n k : ℕ) : RelativeCup.cohomology (fullPair n) k →ₗ[ZMod 2]
    cohomologyZMod2 (Loops n) k :=
  (FullLoopModel.cohomologyEquiv n k).symm.toLinearMap.comp (relativeToPool (fullPair n) k).hom

theorem absolute_injective (n k : ℕ) : Function.Injective (absolute n k) :=
  (FullLoopModel.cohomologyEquiv n k).symm.injective.comp
    (ConstantSublevelRetract.full_relative_injective n k)

theorem lift_absolute (n k : ℕ) (b : RelativeCup.cohomology (fullPair n) k) :
    lift n k (absolute n k b) = b := by
  change RetractedPairCohomology.lift (fullPair n) _ _ k
    ((FullLoopModel.cohomologyEquiv n k) ((FullLoopModel.cohomologyEquiv n k).symm
      ((relativeToPool (fullPair n) k).hom b))) = b
  rw [LinearEquiv.apply_symm_apply, RetractedPairCohomology.lift_relativeToPool]

theorem full_restriction_zero (n k : ℕ) (a : cohomologyZMod2 (Loops n) k)
    (ha : (cohPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k).hom a = 0) :
    (cohPullback (fullPair n).map k).hom (FullLoopModel.cohomologyEquiv n k a) = 0 := by
  have hc : cohPullback ((fullPair n).map ≫ FullLoopModel.forget n) k =
      cohPullback (FullLoopModel.forget n) k ≫ cohPullback (fullPair n).map k :=
    (singularCohomologyZMod2 k).map_comp _ _
  rw [FullLoopModel.constant_square] at hc
  change (cohPullback (FullLoopModel.forget n) k ≫ cohPullback (fullPair n).map k).hom a = 0
  rw [← hc]
  exact ha

theorem lift_spec (n k : ℕ) (a : cohomologyZMod2 (Loops n) k)
    (ha : (cohPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k).hom a = 0) :
    (relativeToPool (fullPair n) k).hom (lift n k a) = FullLoopModel.cohomologyEquiv n k a :=
  RetractedPairCohomology.lift_spec (fullPair n) _ _ k _ (full_restriction_zero n k a ha)

theorem absolute_lift (n k : ℕ) (a : cohomologyZMod2 (Loops n) k)
    (ha : (cohPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k).hom a = 0) :
    absolute n k (lift n k a) = a := by
  change (FullLoopModel.cohomologyEquiv n k).symm
    ((relativeToPool (fullPair n) k).hom (lift n k a)) = a
  rw [lift_spec n k a ha, LinearEquiv.symm_apply_apply]

theorem old_lift_eq (n k : ℕ) (hk : n + 1 < k) (a : cohomologyZMod2 (Loops n) k) :
    ConstantRelativeLift.lift n k hk a = lift n k a := by
  apply ConstantSublevelRetract.full_relative_injective n k
  rw [ConstantRelativeLift.lift_spec,
    lift_spec n k a (ConstantRelativeLift.restriction_zero n k (by omega) (by omega) a)]

theorem pairing (n k : ℕ) (a : cohomologyZMod2 (Loops n) k)
    (ha : (cohPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k).hom a = 0)
    (z : homologyZMod2 (Loops n) k) :
    RelativeKronecker.comparison (fullPair n) k (lift n k a)
      (ConstantRelativePairing.homologyToRelative n k z) = (kroneckerMap (Loops n) k).hom a z := by
  have h := congrArg
    (fun f : Module.Dual (ZMod 2) (homologyZMod2 (fullPair n).fst k) =>
      f ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z))
    (RelativeKronecker.fromRelative_comparison (fullPair n) k (lift n k a))
  change RelativeKronecker.comparison (fullPair n) k (lift n k a)
    (ConstantRelativePairing.homologyToRelative n k z) = (kroneckerMap (fullPair n).fst k).hom
      ((relativeToPool (fullPair n) k).hom (lift n k a))
        ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z) at h
  rw [lift_spec n k a ha, FullLoopModel.cohomology_apply, kroneckerMap_naturality_apply] at h
  change RelativeKronecker.comparison (fullPair n) k (lift n k a)
    (ConstantRelativePairing.homologyToRelative n k z) = (kroneckerMap (Loops n) k).hom a
      ((HomologicalComplex.homologyMap (push (FullLoopModel.forget n)) k).hom
        ((HomologicalComplex.homologyMap (push (FullLoopModel.insert n)) k).hom z)) at h
  rw [ConstantRelativePairing.homology_roundtrip] at h
  exact h

end
end Finsler.FullRelativeSplit
