module

public import Finsler.Loop.RelativeHomologyIsoCohomology
public import TauCeti.AlgebraicTopology.Singular.Excision

/-! A continuous map need only be an ACTUAL isomorphism on patches
containing the relative support. Pinned TauCeti excision then makes
its real global support-pair homology and cohomology maps invertible.
All pair maps and their exact excision square are retained. -/
@[expose] public section
namespace Finsler.RelativeSupportPatchExcision
open CategoryTheory Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {U B : Set X} {V C : Set Y}
  (hU : Set.MapsTo f U V) (hB : Set.MapsTo f B C)
  (hX : interior U ∪ interior B = Set.univ) (hY : interior V ∪ interior C = Set.univ)
  [IsIso (TopPair.interPairMap f hU hB)]

include hU hX hY in
theorem homology_isIso (q : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hB) coeff q) := by
  have hs := TopPair.interPairMap_comp_excisionMap f hU hB
  have hleft : IsIso (TopPair.singularHomologyMap (TopPair.excisionMap U B) coeff q) :=
    TopPair.isIso_singularHomologyMap_excisionMap coeff U B hX q
  have hright : IsIso (TopPair.singularHomologyMap (TopPair.excisionMap V C) coeff q) :=
    TopPair.isIso_singularHomologyMap_excisionMap coeff V C hY q
  have hpatch : IsIso (TopPair.singularHomologyMap (TopPair.interPairMap f hU hB) coeff q) := by
    have hfun : IsIso ((TopPair.singularHomologyFunctor coeff q).map (TopPair.interPairMap f hU hB)) := inferInstance
    rw [TopPair.singularHomologyFunctor_map] at hfun
    have hmid : IsIso (TopPair.singularHomologyMap (TopPair.interPairMap f hU hB) coeff q ≫
        eqToHom (TopPair.singularHomologyFunctor_obj (TopPair.interPair V C) coeff q).symm) :=
      IsIso.of_isIso_comp_left (eqToHom (TopPair.singularHomologyFunctor_obj (TopPair.interPair U B) coeff q)) _
    exact IsIso.of_isIso_comp_right _ (eqToHom (TopPair.singularHomologyFunctor_obj (TopPair.interPair V C) coeff q).symm)
  have hs' := congrArg (fun a => TopPair.singularHomologyMap a coeff q) hs
  rw [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp] at hs'
  have hc : IsIso (TopPair.singularHomologyMap (TopPair.excisionMap U B) coeff q ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap f hB) coeff q) := by
    rw [← hs']
    infer_instance
  exact IsIso.of_isIso_comp_left (TopPair.singularHomologyMap (TopPair.excisionMap U B) coeff q) _

include hU hX hY in
theorem cohomology_bijective (q : ℕ) : Function.Bijective
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (TopPair.ofSubsetMap f hB) q).hom := by
  have := homology_isIso f hU hB hX hY q
  exact RelativeHomologyIsoCohomology.bijective (TopPair.ofSubsetMap f hB) q

include hU hX hY in
def cohomologyEquiv (q : ℕ) : RelativeCup.cohomology (TopPair.ofSubset C) q ≃ₗ[ZMod 2]
    RelativeCup.cohomology (TopPair.ofSubset B) q := by
  have := homology_isIso f hU hB hX hY q
  exact RelativeHomologyIsoCohomology.equiv (TopPair.ofSubsetMap f hB) q

include hU hX hY in
theorem cohomologyEquiv_apply (q : ℕ) (a : RelativeCup.cohomology (TopPair.ofSubset C) q) :
    cohomologyEquiv f hU hB hX hY q a =
      (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (TopPair.ofSubsetMap f hB) q).hom a := by
  have := homology_isIso f hU hB hX hY q
  exact RelativeHomologyIsoCohomology.equiv_apply (TopPair.ofSubsetMap f hB) q a

end
end Finsler.RelativeSupportPatchExcision
