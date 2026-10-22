module

public import Finsler.Loop.MeridianPrimitiveNonzero
public import TauCeti.AlgebraicTopology.Sphere.Puncture
public import TauCeti.AlgebraicTopology.Singular.Contractible

/-! Reuse the ACTUAL pinned TauCeti punctured-sphere contraction on
the ORIGINAL equator via its proved orthogonal-sphere homeomorphism.
Every positive-degree equator class pulls back toZERO along ANY
actual family avoiding one specified direction. This kills the
repeated meridian directions on localized native carriers, without
assuming a local Thom multiplicity or a loop-space rank. -/
@[expose] public section
namespace Finsler.PuncturedEquatorCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

abbrev punctured {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.{0} :=
  TopCat.of ({MeridianEquatorHomology.toOrthogonal P v₀}ᶜ :
    Set (MeridianEquatorHomology.orthogonalSphere P))

def inclusion {n : ℕ} (P : Sphere n) (v₀ : equator P) : punctured P v₀ ⟶ TopCat.of (equator P) :=
  TopCat.ofHom ⟨fun z => (MeridianEquatorHomology.homeomorph P).symm z.val,
    (MeridianEquatorHomology.homeomorph P).symm.continuous.comp continuous_subtype_val⟩

def lift {n : ℕ} (P : Sphere n) (v₀ : equator P) {X : TopCat.{0}} (f : X ⟶ TopCat.of (equator P))
    (hf : ∀ x, f x ≠ v₀) : X ⟶ punctured P v₀ :=
  TopCat.ofHom ⟨fun x => ⟨(MeridianEquatorHomology.homeomorph P) (f x), by
    change (MeridianEquatorHomology.homeomorph P) (f x) ≠ (MeridianEquatorHomology.homeomorph P) v₀
    intro h
    exact hf x ((MeridianEquatorHomology.homeomorph P).injective h)⟩,
    ((MeridianEquatorHomology.homeomorph P).continuous.comp f.hom.continuous).subtype_mk _⟩

theorem factor {n : ℕ} (P : Sphere n) (v₀ : equator P) {X : TopCat.{0}} (f : X ⟶ TopCat.of (equator P))
    (hf : ∀ x, f x ≠ v₀) : f = lift P v₀ f hf ≫ inclusion P v₀ := by
  ext x : 1
  exact ((MeridianEquatorHomology.homeomorph P).symm_apply_apply (f x)).symm

theorem positive_homology_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0) :
    IsZero (homologyZMod2 (punctured P v₀) q) := by
  let : ContractibleSpace (punctured P v₀) :=
    TauCeti.contractibleSpace_sphere_compl_singleton (MeridianEquatorHomology.toOrthogonal P v₀)
  exact TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace
    (C := ModuleCat.{0} (ZMod 2)) coeff (punctured P v₀) hq

theorem homologyPush_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) {X : TopCat.{0}}
    (f : X ⟶ TopCat.of (equator P)) (hf : ∀ x, f x ≠ v₀) (q : ℕ) (hq : q ≠ 0) :
    homologyPushZMod2 f q = 0 := by
  have hg : homologyPushZMod2 (lift P v₀ f hf) q = 0 :=
    (positive_homology_zero P v₀ q hq).eq_of_tgt _ _
  rw [factor P v₀ f hf]
  change ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).map
    (lift P v₀ f hf ≫ inclusion P v₀) = 0
  rw [Functor.map_comp]
  change homologyPushZMod2 (lift P v₀ f hf) q ≫ homologyPushZMod2 (inclusion P v₀) q = 0
  rw [hg, zero_comp]

theorem pullback_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) {X : TopCat.{0}}
    (f : X ⟶ TopCat.of (equator P)) (hf : ∀ x, f x ≠ v₀) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (TopCat.of (equator P)) q) : (cohPullback f q).hom a = 0 := by
  apply kroneckerMap_injective X q
  rw [kroneckerMap_naturality_apply, homologyPush_zero P v₀ f hf q hq]
  simp only [ModuleCat.hom_zero, LinearMap.comp_zero, map_zero]

theorem primitive_pullback_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) {X : TopCat.{0}}
    (f : X ⟶ TopCat.of (equator P)) (hf : ∀ x, f x ≠ v₀) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (f ≫ ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a) = 0 := by
  have hc := ConcreteCategory.congr_hom
    ((singularCohomologyZMod2 q).map_comp (ordinary P v₀).op f.op) (ContinuousLoopSweep.transgression n q a)
  exact hc.trans (pullback_zero P v₀ f hf q hq _)

end
end Finsler.PuncturedEquatorCohomology
