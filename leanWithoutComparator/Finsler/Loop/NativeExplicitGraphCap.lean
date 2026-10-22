module

public import Finsler.Loop.NativeGraphLocalCapReduction
public import Finsler.Loop.NormalizedSphereGraphCap

/-! An EXPLICIT global graph supported-cap cocycle using the SAME
normalized diagonal, the actual remaining-equator primitive and the
SAME localized first-point sphere top cocycle. Its genuine quarter
support and relative lift are proved; no native class value is assigned. -/
@[expose] public section
namespace Finsler.NativeExplicitGraphCap
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativePairRelativeSphereTransport Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev tail {n : ℕ} (P : Sphere n) : TopCat.{0} :=
  BorelEvaluation.sphere n ⊗ TopCat.of (equator P)
abbrev second {n : ℕ} (P : Sphere n) := fst (BorelEvaluation.sphere n) (TopCat.of (equator P))
abbrev first {n : ℕ} (P : Sphere n) := fst (BorelEvaluation.sphere n) (tail P)
def remaining {n : ℕ} (P : Sphere n) : graphSpace P ⟶ TopCat.of (equator P) :=
  snd (BorelEvaluation.sphere n) (tail P) ≫ snd (BorelEvaluation.sphere n) (TopCat.of (equator P))

abbrev exterior {n : ℕ} (P : Sphere n) (ρ : ℝ) := NormalizedSphereGraphCap.exterior n (tail P) (second P) ρ
abbrev near {n : ℕ} (P : Sphere n) (r : ℝ) := NormalizedSphereGraphCap.neighborhood n (tail P) (second P) r
abbrev nearInclusion {n : ℕ} (P : Sphere n) (r : ℝ) := SupportedCap.subspaceMap (graphSpace P) (near P r)
abbrev operation (m : ℕ) (P : Sphere (m + 1)) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :=
  NormalizedSphereGraphCap.operation (m + 1) (by omega) (tail P) (second P) hρ hρr

def remainingCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  cochainPullback (remaining P) m (classRepr (TopCat.of (equator P)) m (LocalNativeBallPrimitive.remainingClass m P v₀))

def evaluationCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :=
  cochainPullback (first P) (m + 1)
    (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη)

theorem remaining_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    cochainCoboundary (ZMod 2) (graphSpace P) m (remainingCocycle m P v₀) = 0 :=
  cochainPullback_cocycle (remaining P) m _ (classRepr_isCocycle _ m _)

theorem evaluation_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (graphSpace P) (m + 1) (evaluationCocycle m P v₀ hη) = 0 :=
  cochainPullback_cocycle (first P) (m + 1) _ (LocalizedSphereTopCocycle.closed _ (by omega) _ hη)

def split (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :=
  cochainCup m (m + 1) (remainingCocycle m P v₀) (evaluationCocycle m P v₀ hη)

theorem split_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (graphSpace P) (m + (m + 1)) (split m P v₀ hη) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _ (remaining_closed m P v₀) (evaluation_closed m P v₀ hη)

def cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :=
  (operation m P hρ hρr).component (m + (m + 1)) ≫
    cochainPullback (nearInclusion P r) (m + (m + 1)) (split m P v₀ hη)

theorem cochain_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (graphSpace P) ((m + 1) + (m + (m + 1))) (cochain m P v₀ hρ hρr hη) = 0 :=
  DegreeLoweringCochainPullback.closed (operation m P hρ hρr) _ _
    (cochainPullback_cocycle (nearInclusion P r) _ _ (split_closed m P v₀ hη))

theorem near_first_far {n : ℕ} (P : Sphere n) (v₀ : equator P) {r η : ℝ}
    (hηr : η + r ≤ 1 / 4) (z : near P r) (hz : z.val ∉ NativeQuarterGraphPatch.graphGood P v₀) :
    η ≤ ‖(z.val.1 : Ambient n) - (LocalNativeBallCut.center P v₀ : Ambient n)‖ := by
  have hd : ‖(z.val.2.1 : Ambient n) - (z.val.1 : Ambient n)‖ < r := z.property
  have hr : 0 < r := (norm_nonneg _).trans_lt hd
  by_cases h : ‖(z.val.1 : Ambient n) - (LocalNativeBallCut.center P v₀ : Ambient n)‖ < 1 / 4
  · have hf : (1 / 4 : ℝ) ≤ ‖(z.val.2.1 : Ambient n) - (LocalNativeBallCut.center P v₀ : Ambient n)‖ :=
      le_of_not_gt (fun h₂ => hz ⟨h, h₂⟩)
    have ht := norm_add_le ((z.val.2.1 : Ambient n) - z.val.1)
      ((z.val.1 : Ambient n) - (LocalNativeBallCut.center P v₀ : Ambient n))
    rw [sub_add_sub_cancel] at ht
    linarith
  · have hf := le_of_not_gt h
    linarith

theorem split_far_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η)
    {X : TopCat.{0}} (f : X ⟶ graphSpace P)
    (hf : ∀ x, η ≤ ‖((f x).1 : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖) :
    cochainPullback f (m + (m + 1)) (split m P v₀ hη) = 0 := by
  have he : cochainPullback f (m + 1) (evaluationCocycle m P v₀ hη) = 0 := by
    rw [evaluationCocycle, ← pullback_comp]
    exact LocalizedSphereTopCocycle.pullback_far_zero (by omega) _ hη (f ≫ first P) hf
  rw [split, cochainCup_naturality, he, cochainCup_zero_right]

theorem outside_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    cochainPullback (SupportedCap.subspaceMap (graphSpace P) (NativeQuarterGraphPatch.graphGood P v₀)ᶜ)
      ((m + 1) + (m + (m + 1))) (cochain m P v₀ hρ hρr hη) = 0 := by
  let X := graphSpace P
  let C := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ
  let f := restriction (SupportedCap.subspaceMap X C)
    ((SupportedCap.subspaceMap X C) ⁻¹' near P r) (near P r) (fun _ h => h)
  have hz := split_far_zero m P v₀ hη (f ≫ nearInclusion P r)
    (fun x => near_first_far P v₀ hηr (f x) x.val.property)
  rw [pullback_comp] at hz
  exact SupportedCutCochainCarrierZero.subspace_cochain_zero X (exterior P ρ) (near P r) C
    (NormalizedSphereGraphCap.exterior_open _ _ _ ρ) (NormalizedSphereGraphCap.neighborhood_open _ _ _ r)
    (NormalizedSphereGraphCap.cover _ _ _ hρr) (m + 1) (m + (m + 1))
    (NormalizedSphereGraphCap.cocycle _ (by omega) (tail P) (second P) hρ)
    (NormalizedSphereGraphCap.cocycle_supported _ (by omega) _ _ hρ)
    (cochainPullback (nearInclusion P r) _ (split m P v₀ hη)) hz

def relativeCocycle (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :=
  (RelativeCupCochain.exists_lift (NativeQuarterGraphDescent.graphSupportPair P v₀) _
    (cochain m P v₀ hρ hρr hη) (outside_zero m P v₀ hρ hρr hη hηr)).choose

theorem relative_ambient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.toAmbient (NativeQuarterGraphDescent.graphSupportPair P v₀) _
      (relativeCocycle m P v₀ hρ hρr hη hηr) = cochain m P v₀ hρ hρr hη :=
  (RelativeCupCochain.exists_lift (NativeQuarterGraphDescent.graphSupportPair P v₀) _
    (cochain m P v₀ hρ hρr hη) (outside_zero m P v₀ hρ hρr hη hηr)).choose_spec

theorem relative_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.differential (NativeQuarterGraphDescent.graphSupportPair P v₀) _
      (relativeCocycle m P v₀ hρ hρr hη hηr) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (NativeQuarterGraphDescent.graphSupportPair P v₀) _
  rw [RelativeCupCochain.toAmbient_differential, relative_ambient, map_zero]
  exact cochain_closed m P v₀ hρ hρr hη

def supportClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :=
  CochainClass.classOf (RelativeCup.cx (NativeQuarterGraphDescent.graphSupportPair P v₀)) _
    (relativeCocycle m P v₀ hρ hρr hη hηr) (relative_closed m P v₀ hρ hρr hη hηr)

end
end Finsler.NativeExplicitGraphCap
