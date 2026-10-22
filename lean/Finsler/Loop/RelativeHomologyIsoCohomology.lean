module

public import Finsler.Topology.RelativeKronecker
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Transport an ACTUAL relative homology isomorphism to the ACTUAL
relative cohomology pullback via pinned TauCeti Kronecker equivalences.
This works without finite-dimensionality or a postulated cohomology
excision axiom. -/
@[expose] public section
namespace Finsler.RelativeHomologyIsoCohomology
open CategoryTheory Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {P Q : TopPair.{0}} (f : P ⟶ Q) (q : ℕ)
  [IsIso (TopPair.singularHomologyMap f coeff q)]

def equiv : RelativeCup.cohomology Q q ≃ₗ[ZMod 2] RelativeCup.cohomology P q :=
  (RelativeKronecker.equiv Q q).trans
    (((asIso (TopPair.singularHomologyMap f coeff q)).toLinearEquiv.dualMap).trans
      (RelativeKronecker.equiv P q).symm)

theorem equiv_apply (a : RelativeCup.cohomology Q q) :
    equiv f q a = (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom a := by
  apply (RelativeKronecker.equiv P q).injective
  rw [RelativeKronecker.equiv_natural]
  simp only [equiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem bijective : Function.Bijective
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom := by
  have he : (equiv f q : RelativeCup.cohomology Q q → RelativeCup.cohomology P q) =
      (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom :=
    funext (equiv_apply f q)
  rw [← he]
  exact (equiv f q).bijective

end
end Finsler.RelativeHomologyIsoCohomology
