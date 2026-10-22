module

public import Finsler.Loop.CanonicalGlobalTimeCup

/-! Bundle the SINGLE actual time cup as a bilinear map, including its
native degree transport. Bilinearity comes from actual ordinary cup
and the proved linear cohomology map, rather than algebra fields. -/

@[expose] public section
namespace Finsler.CanonicalTimeCupBilinear
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem cup_right_apply (X : TopCat.{0}) (p q : ℕ)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    cupZMod2 a b = (cupHomologyRight X p q (classRepr X p a) (classRepr_isCocycle X p a)).hom b := by
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective X q b
  have h := cupZMod2_mk (classRepr X p a) (classRepr_isCocycle X p a) ψ hψ
  rw [cocycleClass_classRepr] at h
  exact h.trans (cupHomologyRight_apply X p q (classRepr X p a) (classRepr_isCocycle X p a) ψ hψ).symm

def cupBilinear (X : TopCat.{0}) (p q : ℕ) :
    cohomologyZMod2 X p →ₗ[ZMod 2] cohomologyZMod2 X q →ₗ[ZMod 2] cohomologyZMod2 X (p + q) where
  toFun a :=
    { toFun := cupZMod2 a
      map_add' := by intros; simp only [cup_right_apply, map_add]
      map_smul' := by intros; simp only [cup_right_apply, map_smul, RingHom.id_apply] }
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    exact map_add (cupHomologyLeft X p q (classRepr X q b) (classRepr_isCocycle X q b)).hom a a'
  map_smul' c a := by
    apply LinearMap.ext
    intro b
    exact map_smul (cupHomologyLeft X p q (classRepr X q b) (classRepr_isCocycle X q b)).hom c a

def castLinear (X : TopCat.{0}) {i j : ℕ} (h : i = j) :
    cohomologyZMod2 X i →ₗ[ZMod 2] cohomologyZMod2 X j := by
  subst j
  exact LinearMap.id

theorem cast_apply (X : TopCat.{0}) {i j : ℕ} (h : i = j) (a : cohomologyZMod2 X i) :
    castLinear X h a = CupUnit.absoluteCast X h a := by
  subst j
  rfl

def bilinear (m p q : ℕ) :
    cohomologyZMod2 (Loops (m + 1)) p →ₗ[ZMod 2]
      cohomologyZMod2 (Loops (m + 1)) q →ₗ[ZMod 2] cohomologyZMod2 (Loops (m + 1)) ((m + p) + q) :=
  let X := Loops (m + 1)
  let Y := TopCat.of (SupportedSelfCut.neighborhood (m + 1) (1 / 2 : ℝ))
  let J := (cohPullback (TopCat.ofHom (SupportedSelfCut.tested (m + 1) (by norm_num : (1 / 2 : ℝ) ≤ 1))) p).hom
  let K := (cohPullback (TopCat.ofHom (SupportedSelfCut.retained (m + 1) (by norm_num : (1 / 2 : ℝ) ≤ 1))) q).hom
  let C := DegreeLoweringCohomologyPullback.map (GlobalThomTime.operation m
    (by norm_num : 0 < (1 / 4 : ℝ)) (by norm_num : (1 / 4 : ℝ) < 1 / 2)) (p + q)
  let A := castLinear X (Nat.add_assoc m p q).symm
  { toFun a := A.comp (C.comp ((cupBilinear Y p q (J a)).comp K))
    map_add' := by
      intro a a'
      apply LinearMap.ext
      intro b
      change A (C (cupBilinear Y p q (J (a + a')) (K b))) =
        A (C (cupBilinear Y p q (J a) (K b))) + A (C (cupBilinear Y p q (J a') (K b)))
      simp only [map_add, LinearMap.add_apply]
    map_smul' := by
      intro c a
      apply LinearMap.ext
      intro b
      change A (C (cupBilinear Y p q (J (c • a)) (K b))) =
        c • A (C (cupBilinear Y p q (J a) (K b)))
      simp only [map_smul, LinearMap.smul_apply] }

theorem bilinear_apply (m p q : ℕ) (a : cohomologyZMod2 (Loops (m + 1)) p)
    (b : cohomologyZMod2 (Loops (m + 1)) q) :
    bilinear m p q a b = CanonicalGlobalTimeCup.product m p q a b := by
  change castLinear (Loops (m + 1)) (Nat.add_assoc m p q).symm _ = _
  rw [cast_apply]
  rfl

def relativeBilinear (m p q : ℕ) (hk : (m + 1) + 1 < (m + p) + q) :
    RelativeCup.cohomology (fullPair (m + 1)) p →ₗ[ZMod 2]
      RelativeCup.cohomology (fullPair (m + 1)) q →ₗ[ZMod 2]
        RelativeCup.cohomology (fullPair (m + 1)) ((m + p) + q) :=
  let A := RelativeTimeCup.absolute (m + 1) p
  let B := RelativeTimeCup.absolute (m + 1) q
  let L := ConstantRelativeLift.lift (m + 1) ((m + p) + q) hk
  { toFun a := L.comp ((bilinear m p q (A a)).comp B)
    map_add' := by
      intro a a'
      apply LinearMap.ext
      intro b
      simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
    map_smul' := by
      intro c a
      apply LinearMap.ext
      intro b
      simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply] }

theorem relative_bilinear_apply (m p q : ℕ) (hk : (m + 1) + 1 < (m + p) + q)
    (a : RelativeCup.cohomology (fullPair (m + 1)) p)
    (b : RelativeCup.cohomology (fullPair (m + 1)) q) :
    relativeBilinear m p q hk a b = CanonicalGlobalTimeCup.relativeProduct m p q hk a b := by
  change ConstantRelativeLift.lift (m + 1) ((m + p) + q) hk (bilinear m p q _ _) = _
  rw [bilinear_apply]
  rfl

end
end Finsler.CanonicalTimeCupBilinear
