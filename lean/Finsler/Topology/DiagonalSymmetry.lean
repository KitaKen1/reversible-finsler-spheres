module

public import Finsler.Topology.DiagonalUniqueness

/-! The actual diagonal relative class is invariant under exchanging factors.
The uniqueness argument applies in all dimensions at least two. -/

@[expose] public section

namespace Finsler.DiagonalSymmetry

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.DiagonalGeometry Finsler.SphereTopClass
open Finsler.BorelEvaluation Finsler.CochainComparison
open Finsler.DiagonalCohomology Finsler.DiagonalUniqueness

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def exchange (n : ℕ) : product n ⟶ product n :=
  TopCat.ofHom ⟨Prod.swap, continuous_swap⟩

def exchangePair (n : ℕ) : diagonalPair n ⟶ diagonalPair n :=
  TopPair.ofSubsetMap (B := deleted n) (B' := deleted n) (exchange n) (by
    intro x hx
    exact Ne.symm hx)

theorem exchangePair_fst (n : ℕ) : TopPair.Hom.fst (exchangePair n) = exchange n := by
  ext x : 1
  exact TopPair.ofSubsetMap_fst_apply (B := deleted n) (B' := deleted n) (exchange n)
    (by intro z hz; exact Ne.symm hz) x

theorem exchange_involution (n : ℕ) : exchange n ≫ exchange n = 𝟙 (product n) := by
  ext x : 1
  rfl

theorem exchange_first (n : ℕ) : exchange n ≫ prFirst n = prSecond n := by
  ext x : 1
  rfl

theorem exchange_second (n : ℕ) : exchange n ≫ prSecond n = prFirst n := by
  ext x : 1
  rfl

theorem ambientClass_exchange (n : ℕ) (hn : 1 ≤ n) :
    (cohPullback (exchange n) n).hom (ambientClass n hn) = ambientClass n hn := by
  unfold ambientClass
  rw [map_add, ← Cup.pullback_comp, ← Cup.pullback_comp,
    exchange_first, exchange_second, add_comm]

theorem relativeClass_exchange (n : ℕ) (hn : 2 ≤ n) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (exchangePair n) n).hom (relativeClass n (by omega)) = relativeClass n (by omega) := by
  apply relative_image_injective n hn
  have he := congrArg (fun f => f.hom (relativeClass n (by omega)))
    (relative_to_absolute_natural (exchangePair n) n)
  have hp : (relativeToPool (diagonalPair n) n).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (exchangePair n) n).hom (relativeClass n (by omega))) =
        (relativeToPool (diagonalPair n) n).hom (relativeClass n (by omega)) := by
    calc
      _ = (cohPullback (TopPair.Hom.fst (exchangePair n)) n).hom
          ((relativeToPool (diagonalPair n) n).hom (relativeClass n (by omega))) := he
      _ = (cohPullback (exchange n) n).hom (ambientClass n (by omega)) := by
        rw [exchangePair_fst, relativeClass_pool_image]
        rfl
      _ = ambientClass n (by omega) := ambientClass_exchange n (by omega)
      _ = _ := (relativeClass_pool_image n (by omega)).symm
  exact (Finsler.CochainComparison.cohomologyEquiv (product n) n).symm.injective hp


end
end Finsler.DiagonalSymmetry
