module

public import Finsler.Loop.CupAtDegree
public import Finsler.Loop.ContinuousLoopHomologyEquivalence
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Transport ordinary cup-square vanishing through ACTUAL induced
homology maps. Over F2 an injective homology map gives a surjective
cohomology pullback by the genuine Kronecker isomorphism. -/
@[expose] public section
namespace Finsler.CupSquareZeroTransport
open CategoryTheory AlgebraicTopology SphereOddDegree Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem pullback_surjective {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (hf : Function.Injective (homologyPushZMod2 f q).hom) :
    Function.Surjective (cohPullback f q).hom := by
  obtain ⟨g, hg⟩ := (homologyPushZMod2 f q).hom.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  intro a
  obtain ⟨b, hb⟩ := kroneckerMap_surjective Y q (((kroneckerMap X q).hom a).comp g)
  refine ⟨b, ?_⟩
  apply kroneckerMap_injective
  rw [kroneckerMap_naturality_apply, hb, LinearMap.comp_assoc, hg, LinearMap.comp_id]

theorem pullback_injective {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (hf : Function.Surjective (homologyPushZMod2 f q).hom) :
    Function.Injective (cohPullback f q).hom := by
  intro a b hab
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := hf z
  have he := congrArg (fun c => (kroneckerMap X q).hom c w) hab
  exact (congrArg (fun l => l w) (kroneckerMap_naturality_apply f q a)).symm.trans
    (he.trans (congrArg (fun l => l w) (kroneckerMap_naturality_apply f q b)))

theorem along_injective_homology {X Y : TopCat.{0}} (f : X ⟶ Y) (m : ℕ)
    (hf : Function.Injective (homologyPushZMod2 f m).hom)
    (hY : ∀ a : cohomologyZMod2 Y m, cupZMod2 a a = 0)
    (a : cohomologyZMod2 X m) : cupZMod2 a a = 0 := by
  obtain ⟨b, rfl⟩ := pullback_surjective f m hf a
  rw [← Cup.naturality, hY, map_zero]

theorem detected_by_surjective_homology {X Y : TopCat.{0}} (f : X ⟶ Y) (m : ℕ)
    (hf : Function.Surjective (homologyPushZMod2 f (m + m)).hom)
    (hX : ∀ a : cohomologyZMod2 X m, cupZMod2 a a = 0)
    (a : cohomologyZMod2 Y m) : cupZMod2 a a = 0 := by
  apply pullback_injective f (m + m) hf
  rw [map_zero, Cup.naturality, hX]

theorem equal_of_one_value (X : TopCat.{0}) (q : ℕ)
    (hd : Module.finrank (ZMod 2) (homologyZMod2 X q) = 1)
    (z : homologyZMod2 X q) (hz : z ≠ 0)
    (a b : cohomologyZMod2 X q)
    (he : (kroneckerMap X q).hom a z = (kroneckerMap X q).hom b z) : a = b := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro w
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hd hz w
  rw [map_smul, map_smul, he]

end
end Finsler.CupSquareZeroTransport
