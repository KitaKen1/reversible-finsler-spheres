module

public import Finsler.Topology.RelativeDual
public import Mathlib.Algebra.Field.ZMod
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.KroneckerNaturality

/-! Reuse the natural universal-coefficient isomorphism of Lean Pool over F₂.
Its absolute chain model agrees with the ambient part of Tau Ceti's relative
chain model. This provides genuine relative dual lifts for absolute classes;
RelativeKronecker separately provides the full relative comparison and cup
pairing. Equivariant comparisons remain separate. -/

@[expose] public section

namespace Finsler.Kronecker

open CategoryTheory SphereOddDegree

noncomputable section

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem comparison_bijective (X : TopCat.{0}) (n : ℕ) :
    Function.Bijective (kroneckerMap X n).hom := kroneckerMap_bijective X n

theorem comparison_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : cohomologyZMod2 Y n) :
    (kroneckerMap X n).hom ((cohPullback f n).hom a) =
      ((kroneckerMap Y n).hom a).comp (homologyPushZMod2 f n).hom :=
  kroneckerMap_naturality_apply f n a

/-- The classifiers on the subspace and ambient space use the same chain maps
as the actual relative pair. The identity below is checked without a comparison
assumption or a finite-dimensionality assumption. -/
theorem restriction_comparison (P : TopPair.{0}) (n : ℕ)
    (a : cohomologyZMod2 P.fst n) :
    Finsler.RelativeDual.restrict (ZMod 2) P n ((kroneckerMap P.fst n).hom a) =
      (kroneckerMap P.snd n).hom ((cohPullback P.map n).hom a) := by
  exact (comparison_natural P.map n a).symm

/-- An absolute class restricting to zero on the subspace has a relative lift
in the dual homology model, using the actual inclusion of every TopPair. -/
theorem relative_lift_of_pullback_zero (P : TopPair.{0}) (n : ℕ)
    (a : cohomologyZMod2 P.fst n) (ha : (cohPullback P.map n).hom a = 0) :
    ∃ ψ : Finsler.RelativeDual.relative (ZMod 2) P n,
      Finsler.RelativeDual.fromRelative (ZMod 2) P n ψ = (kroneckerMap P.fst n).hom a := by
  apply Finsler.RelativeDual.lift_of_restriction_zero
  rw [restriction_comparison, ha, map_zero]
  rfl

end

end Finsler.Kronecker
