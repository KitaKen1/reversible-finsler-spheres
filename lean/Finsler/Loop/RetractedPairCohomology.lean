module

public import Finsler.Loop.RetractedPairChains

/-! The actual relative-to-absolute cohomology map of a retracted
pair is injective in EVERY degree. The genuine chain section gives
a linear cohomology retraction and canonical lifts of all classes
whose restriction is zero, without adjacent-degree vanishing. -/

@[expose] public section
namespace Finsler.RetractedPairCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (P : TopPair.{0}) (r : P.fst ⟶ P.snd) (hr : P.map ≫ r = 𝟙 P.snd)

def cochainRetraction : native P.fst ⟶ P.singularCochainComplex coeff (ZMod 2) coeff :=
  (TauCeti.ChainComplex.linearYonedaFunctor (ZMod 2) coeff).map
    (RetractedPairChains.sectionMap P r hr).op

theorem cochain_left_inverse :
    (P.singularCochainComplexShortComplex coeff (ZMod 2) coeff).f ≫ cochainRetraction P r hr = 𝟙 _ := by
  rw [cochainRetraction, TopPair.singularCochainComplexShortComplex_f_eq,
    ← CategoryTheory.Functor.map_comp, ← op_comp, RetractedPairChains.section_quotient,
    op_id, CategoryTheory.Functor.map_id]
  rfl

theorem native_left_inverse (q : ℕ) :
    P.singularCohomologyπ coeff (ZMod 2) coeff q ≫
      HomologicalComplex.homologyMap (cochainRetraction P r hr) q = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp, cochain_left_inverse, HomologicalComplex.homologyMap_id]

include r hr in
theorem native_injective (q : ℕ) : Function.Injective
    (P.singularCohomologyπ coeff (ZMod 2) coeff q).hom := by
  intro a b h
  have hh := congrArg (HomologicalComplex.homologyMap (cochainRetraction P r hr) q).hom h
  change (P.singularCohomologyπ coeff (ZMod 2) coeff q ≫
    HomologicalComplex.homologyMap (cochainRetraction P r hr) q).hom a =
    (P.singularCohomologyπ coeff (ZMod 2) coeff q ≫
      HomologicalComplex.homologyMap (cochainRetraction P r hr) q).hom b at hh
  rw [native_left_inverse] at hh
  exact hh

include r hr in
theorem relativeToPool_injective (q : ℕ) : Function.Injective (relativeToPool P q).hom := by
  intro a b h
  apply native_injective P r hr q
  apply (cohomologyEquiv P.fst q).symm.injective
  exact h

def lift (q : ℕ) : cohomologyZMod2 P.fst q →ₗ[ZMod 2]
    P.singularCohomology coeff (ZMod 2) coeff q :=
  (HomologicalComplex.homologyMap (cochainRetraction P r hr) q).hom.comp
    (cohomologyEquiv P.fst q).toLinearMap

theorem lift_relativeToPool (q : ℕ) (b : P.singularCohomology coeff (ZMod 2) coeff q) :
    lift P r hr q ((relativeToPool P q).hom b) = b := by
  change (HomologicalComplex.homologyMap (cochainRetraction P r hr) q).hom
    ((cohomologyEquiv P.fst q) ((cohomologyEquiv P.fst q).symm
      ((P.singularCohomologyπ coeff (ZMod 2) coeff q).hom b))) = b
  rw [LinearEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (native_left_inverse P r hr q) b

theorem lift_spec (q : ℕ) (a : cohomologyZMod2 P.fst q)
    (ha : (cohPullback P.map q).hom a = 0) :
    (relativeToPool P q).hom (lift P r hr q a) = a := by
  obtain ⟨b, hb⟩ := relative_lift P q a ha
  have hb' : (relativeToPool P q).hom b = a := by
    change (cohomologyEquiv P.fst q).symm
      ((P.singularCohomologyπ coeff (ZMod 2) coeff q).hom b) = a
    rw [hb]
    exact (cohomologyEquiv P.fst q).symm_apply_apply a
  rw [← hb', lift_relativeToPool]

theorem lift_unique (q : ℕ) (a : cohomologyZMod2 P.fst q)
    (ha : (cohPullback P.map q).hom a = 0)
    (b : P.singularCohomology coeff (ZMod 2) coeff q)
    (hb : (relativeToPool P q).hom b = a) : b = lift P r hr q a := by
  apply relativeToPool_injective P r hr q
  rw [hb, lift_spec P r hr q a ha]

end
end Finsler.RetractedPairCohomology
