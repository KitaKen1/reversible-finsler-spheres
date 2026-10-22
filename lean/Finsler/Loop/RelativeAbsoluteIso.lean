module

public import Finsler.Topology.CochainComparison

/-! The ACTUAL relative-to-absolute map is an isomorphism when the
adjacent subspace cohomology groups vanish. Use Tau Ceti's real long
exact sequence, retaining Lean Pool's absolute cohomology model. -/

@[expose] public section
namespace Finsler.RelativeAbsoluteIso
open CategoryTheory SphereOddDegree Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem surjective (P : TopPair.{0}) (k : ℕ)
    (hsub : Subsingleton (cohomologyZMod2 P.snd k)) :
    Function.Surjective (relativeToPool P k).hom := by
  intro a
  obtain ⟨b, hb⟩ := relative_lift P k a (hsub.elim _ _)
  refine ⟨b, ?_⟩
  change (cohomologyEquiv P.fst k).symm ((P.singularCohomologyπ coeff (ZMod 2) coeff k).hom b) = a
  rw [hb]
  exact (cohomologyEquiv P.fst k).symm_apply_apply a

theorem injective (P : TopPair.{0}) (j k : ℕ) (hk : j + 1 = k)
    (hsub : Subsingleton (cohomologyZMod2 P.snd j)) :
    Function.Injective (relativeToPool P k).hom := by
  intro b c he
  have hz : (P.singularCohomologyπ coeff (ZMod 2) coeff k).hom (b - c) = 0 := by
    apply (cohomologyEquiv P.fst k).symm.injective
    change (relativeToPool P k).hom (b - c) = (cohomologyEquiv P.fst k).symm 0
    rw [map_sub, he, sub_self, map_zero]
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (P.singularCohomology_exact_relative coeff (ZMod 2) coeff j k hk) (b - c) hz
  have hx0 : x = 0 := by
    apply (cohomologyEquiv P.snd j).symm.injective
    exact hsub.elim _ _
  rw [hx0, map_zero] at hx
  exact sub_eq_zero.mp hx.symm

def equiv (P : TopPair.{0}) (j k : ℕ) (hk : j + 1 = k)
    (hprev : Subsingleton (cohomologyZMod2 P.snd j))
    (hsub : Subsingleton (cohomologyZMod2 P.snd k)) :
    P.singularCohomology coeff (ZMod 2) coeff k ≃ₗ[ZMod 2] cohomologyZMod2 P.fst k :=
  LinearEquiv.ofBijective (relativeToPool P k).hom ⟨injective P j k hk hprev, surjective P k hsub⟩

theorem equiv_apply (P : TopPair.{0}) (j k : ℕ) (hk : j + 1 = k)
    (hprev : Subsingleton (cohomologyZMod2 P.snd j))
    (hsub : Subsingleton (cohomologyZMod2 P.snd k))
    (b : P.singularCohomology coeff (ZMod 2) coeff k) :
    equiv P j k hk hprev hsub b = (relativeToPool P k).hom b := rfl

end
end Finsler.RelativeAbsoluteIso
