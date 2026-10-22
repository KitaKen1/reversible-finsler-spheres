module

public import Finsler.Loop.ConstantLoopModel
public import Finsler.Loop.FullLoopModel
public import Finsler.Loop.RelativeAbsoluteIso
public import Finsler.Topology.RelativeCup

/-! Actual high-degree relative classes for the original full loop
pair. Sphere vanishing gives existence away from degrees zero/n;
the adjacent vanishing gives a canonical linear lift above n+1. -/

@[expose] public section
namespace Finsler.ConstantRelativeLift
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem restriction_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n)
    (a : cohomologyZMod2 (Loops n) k) :
    (cohPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k).hom a = 0 :=
  ConstantLoopModel.cohomology_eq_zero n k hk hkn _

theorem full_restriction_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n)
    (a : cohomologyZMod2 (fullPair n).fst k) :
    (cohPullback (fullPair n).map k).hom a = 0 :=
  ConstantLoopModel.cohomology_eq_zero n k hk hkn _

theorem exists_lift (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n)
    (a : cohomologyZMod2 (Loops n) k) :
    ∃ b : RelativeCup.cohomology (fullPair n) k,
      (relativeToPool (fullPair n) k).hom b = (FullLoopModel.cohomologyEquiv n k) a := by
  exact RelativeAbsoluteIso.surjective (fullPair n) k
    (ConstantLoopModel.cohomology_subsingleton n k hk hkn) _

def equiv (n k : ℕ) (hk : n + 1 < k) :
    RelativeCup.cohomology (fullPair n) k ≃ₗ[ZMod 2] cohomologyZMod2 (Loops n) k :=
  (RelativeAbsoluteIso.equiv (fullPair n) (k - 1) k (by omega)
    (ConstantLoopModel.cohomology_subsingleton n (k - 1) (by omega) (by omega))
    (ConstantLoopModel.cohomology_subsingleton n k (by omega) (by omega))).trans
      (FullLoopModel.cohomologyEquiv n k).symm

theorem equiv_apply (n k : ℕ) (hk : n + 1 < k)
    (b : RelativeCup.cohomology (fullPair n) k) :
    equiv n k hk b = (FullLoopModel.cohomologyEquiv n k).symm
      ((relativeToPool (fullPair n) k).hom b) := rfl

def lift (n k : ℕ) (hk : n + 1 < k) :
    cohomologyZMod2 (Loops n) k →ₗ[ZMod 2] RelativeCup.cohomology (fullPair n) k :=
  (equiv n k hk).symm.toLinearMap

theorem lift_spec (n k : ℕ) (hk : n + 1 < k) (a : cohomologyZMod2 (Loops n) k) :
    (relativeToPool (fullPair n) k).hom (lift n k hk a) =
      (FullLoopModel.cohomologyEquiv n k) a := by
  apply (FullLoopModel.cohomologyEquiv n k).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (equiv n k hk).apply_symm_apply a

theorem lift_unique (n k : ℕ) (hk : n + 1 < k) (a : cohomologyZMod2 (Loops n) k)
    (b : RelativeCup.cohomology (fullPair n) k)
    (hb : (relativeToPool (fullPair n) k).hom b = (FullLoopModel.cohomologyEquiv n k) a) :
    b = lift n k hk a := by
  apply (equiv n k hk).injective
  rw [equiv_apply, hb, LinearEquiv.symm_apply_apply]
  exact ((equiv n k hk).apply_symm_apply a).symm

end
end Finsler.ConstantRelativeLift
