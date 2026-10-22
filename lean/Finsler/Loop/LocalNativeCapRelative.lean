module

public import Finsler.Loop.LocalNativeCapCorrection

/-! The ACTUAL source-local first-Thom cap comparison is an equality
in the genuine quarter-supported RELATIVE cohomology, with the actual
post-cap correction as a relative primitive. No absolute lift is used. -/
@[expose] public section
namespace Finsler.LocalNativeCapRelative
open CategoryTheory CategoryTheory.Limits SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def lift {X : TopCat.{0}} (C : Set X) (q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X q)
    (hz : cochainPullback (SupportedCap.subspaceMap X C) q φ = 0) :=
  (RelativeCupCochain.exists_lift (TopPair.ofSubset C) q φ hz).choose

private theorem lift_ambient {X : TopCat.{0}} (C : Set X) (q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X q)
    (hz : cochainPullback (SupportedCap.subspaceMap X C) q φ = 0) :
    RelativeCupCochain.toAmbient (TopPair.ofSubset C) q (lift C q φ hz) = φ :=
  (RelativeCupCochain.exists_lift (TopPair.ofSubset C) q φ hz).choose_spec

private theorem lift_closed {X : TopCat.{0}} (C : Set X) (q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X q)
    (hz : cochainPullback (SupportedCap.subspaceMap X C) q φ = 0)
    (hc : cochainCoboundary (ZMod 2) X q φ = 0) :
    RelativeCupCochain.differential (TopPair.ofSubset C) q (lift C q φ hz) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (TopPair.ofSubset C) (q + 1)
  rw [RelativeCupCochain.toAmbient_differential, lift_ambient, map_zero]
  exact hc

def tested (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :=
  lift (NativeBallSupportPatch.localGood P v₀)ᶜ ((m + 1) + (m + (m + 1)))
    (LocalNativeCapCorrection.testedCochain m P v₀ b hρ hρr hη)
    (LocalNativeCapCorrection.tested_outside_zero m P v₀ b hρ hρr hη hηr)

def reduced (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :=
  lift (NativeBallSupportPatch.localGood P v₀)ᶜ ((m + 1) + (m + (m + 1)))
    (LocalNativeCapCorrection.reducedCochain m P v₀ b hρ hρr hη)
    (LocalNativeCapCorrection.reduced_outside_zero m P v₀ b hρ hρr hη hηr)

def correction (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :=
  lift (NativeBallSupportPatch.localGood P v₀)ᶜ ((m + 1) + ((m - 1) + (m + 1)))
    (LocalNativeCapCorrection.correction m hm P v₀ b hρ hρr hη)
    (LocalNativeCapCorrection.correction_outside_zero m hm P v₀ b hρ hρr hη hηr)

theorem tested_ambient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (tested m P v₀ b hρ hρr hη hηr) =
      LocalNativeCapCorrection.testedCochain m P v₀ b hρ hρr hη := lift_ambient _ _ _ _

theorem reduced_ambient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (reduced m P v₀ b hρ hρr hη hηr) =
      LocalNativeCapCorrection.reducedCochain m P v₀ b hρ hρr hη := lift_ambient _ _ _ _

theorem correction_ambient (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (correction m hm P v₀ b hρ hρr hη hηr) =
      LocalNativeCapCorrection.correction m hm P v₀ b hρ hρr hη := lift_ambient _ _ _ _

theorem tested_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) _ (tested m P v₀ b hρ hρr hη hηr) = 0 :=
  lift_closed _ _ _ _ (LocalNativeCapCorrection.tested_closed m P v₀ b hρ hρr hη)

theorem reduced_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) _ (reduced m P v₀ b hρ hρr hη hηr) = 0 :=
  lift_closed _ _ _ _ (LocalNativeCapCorrection.reduced_closed m P v₀ b hρ hρr hη)

theorem correction_boundary (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) _ (correction m hm P v₀ b hρ hρr hη hηr) =
      RelativeCupCochain.cast (NativeBallSupportPatch.localPair P v₀)
        (by omega : (m + 1) + (m + (m + 1)) = ((m + 1) + ((m - 1) + (m + 1))) + 1)
        (tested m P v₀ b hρ hρr hη hηr - reduced m P v₀ b hρ hρr hη hηr) := by
  apply RelativeCupCochain.toAmbient_injective (NativeBallSupportPatch.localPair P v₀) _
  rw [RelativeCupCochain.toAmbient_differential, correction_ambient,
    RelativeCupCochain.toAmbient_cast, map_sub, tested_ambient, reduced_ambient]
  exact LocalNativeCapCorrection.correction_boundary m hm P v₀ b hρ hρr hη

private theorem class_eq_cast_boundary (P : TopPair.{0}) (i N : ℕ) (h : N = i + 1)
    (η : RelativeCupCochain.relative P i) (φ ψ : RelativeCupCochain.relative P N)
    (hφ : RelativeCupCochain.differential P N φ = 0) (hψ : RelativeCupCochain.differential P N ψ = 0)
    (hb : RelativeCupCochain.differential P i η = RelativeCupCochain.cast P h (φ - ψ)) :
    CochainClass.classOf (RelativeCup.cx P) N φ hφ = CochainClass.classOf (RelativeCup.cx P) N ψ hψ := by
  subst N
  exact RelativeCupCommutativity.classOf_eq_of_boundary (RelativeCup.cx P) i (i + 1) η φ ψ hφ hψ hb.symm

theorem class_eq (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (tested m P v₀ b hρ hρr hη hηr) (tested_closed m P v₀ b hρ hρr hη hηr) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (reduced m P v₀ b hρ hρr hη hηr) (reduced_closed m P v₀ b hρ hρr hη hηr) :=
  class_eq_cast_boundary _ _ _ (by omega) _ _ _ _ _ (correction_boundary m hm P v₀ b hρ hρr hη hηr)

end
end Finsler.LocalNativeCapRelative
