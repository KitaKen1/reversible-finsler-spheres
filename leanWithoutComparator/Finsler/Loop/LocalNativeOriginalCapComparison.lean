module

public import Finsler.Loop.LocalNativeCapRelative
public import Finsler.Loop.NativeQuarterGraphCompatibility
public import Finsler.Loop.SupportedSmallCochainComparison
public import Finsler.Loop.SupportedCapSmallNaturality

/-! Compare the SAME ORIGINAL native supported cut class with the real
source-local cap. Exact equality on source small chains and an actual
support-preserving subdivision-prism primitive prove RELATIVE equality.
This connects the new local cap calculation to the original operation. -/
@[expose] public section
namespace Finsler.LocalNativeOriginalCapComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeMeridianPairCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem maps_support {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (LocalNativeBallCut.toNative P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ
      (NativeQuarterSupport.good P v₀)ᶜ := by
  intro z hz hg
  have hc := ConcreteCategory.congr_hom (LocalNativeBallCut.coordinates P v₀) z
  change sphereCoordinates P (LocalNativeBallCut.toNative P v₀ z) = LocalNativeBallCut.toGraph P v₀ z at hc
  have hpre : sphereCoordinates P (LocalNativeBallCut.toNative P v₀ z) ∈ NativeQuarterGraphPatch.graphGood P v₀ := hg
  rw [hc] at hpre
  exact hz hpre

def toNativePair {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeBallSupportPatch.localPair P v₀ ⟶ NativeQuarterSupport.supportPair P v₀ :=
  TopPair.ofSubsetMap (LocalNativeBallCut.toNative P v₀) (maps_support P v₀)

theorem toNativePair_fst {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Hom.fst (toNativePair P v₀) = LocalNativeBallCut.toNative P v₀ := by
  apply TopCat.ext
  intro z
  exact TopPair.ofSubsetMap_fst_apply (LocalNativeBallCut.toNative P v₀) (maps_support P v₀) z

def original (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  RelativeCupCochain.pullback (toNativePair P v₀) ((m + 1) + (m + (m + 1)))
    (NativeQuarterSupport.relativeCocycle m m P v₀ b hρ hρr hr hη hr8 hη8
      (classRepr (BorelLoop.Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)))

theorem original_ambient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (original m P v₀ b hρ hρr hr hη hr8 hη8) =
      cochainPullback (LocalNativeBallCut.cutParameters P v₀ b) ((m + 1) + (m + (m + 1)))
        (LocalizedParameterCutCochain.cochain m m (LocalNativeBallCut.center P v₀) hρ hρr hr hη
          (classRepr (BorelLoop.Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))) := by
  rw [original, RelativeCupCochain.toAmbient_pullback, NativeQuarterSupport.relative_toAmbient, toNativePair_fst]
  exact (pullback_comp (LocalNativeBallCut.toNative P v₀) (intoCut P v₀ b) _ _).symm

theorem original_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) _ (original m P v₀ b hρ hρr hr hη hr8 hη8) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (toNativePair P v₀)) _ _
    (NativeQuarterSupport.relative_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))

theorem small_cochain_eq (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
        (LocalNativeBallCut.near P v₀ b r))).f ((m + 1) + (m + (m + 1))) ≫
      RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (original m P v₀ b hρ hρr hr hη hr8 hη8) =
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
        (LocalNativeBallCut.near P v₀ b r))).f ((m + 1) + (m + (m + 1))) ≫
      LocalNativeCapCorrection.testedCochain m P v₀ b hρ hρr hη := by
  let X := LocalNativeBallCut.space P v₀
  let Y := SelfCutThomCocycle.parameters (m + 1)
  let f := LocalNativeBallCut.cutParameters P v₀ b
  let A := LocalNativeSupportedCap.exterior P v₀ b ρ
  let B := LocalNativeBallCut.near P v₀ b r
  let C := SupportedSelfCut.exterior (m + 1) ρ
  let D := SupportedSelfCut.neighborhood (m + 1) r
  let T := classRepr (BorelLoop.Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)
  let split := GeometricTimeCupCochain.splitCup m m hr T (m + 1)
    (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη)
  have hn := SupportedCapSmallNaturality.naturality f A B C D
    (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r)
    (LocalNativeSupportedCap.cover P v₀ b hρr) (SupportedSelfCut.exterior_open (m + 1) ρ)
    (SupportedSelfCut.neighborhood_open (m + 1) r) (SupportedSelfCut.cover (m + 1) hρr)
    (fun _ h => h) (fun _ h => h) (m + 1) (m + (m + 1)) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
  have he := congrArg (fun a => a ≫ split) hn
  have hs : (push (restriction f B D (fun _ h => h))).f (m + (m + 1)) ≫ split =
      cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) (m + (m + 1))
        (cochainCup m (m + 1) (LocalNativeBallPrimitive.testedCocycle m P v₀ b)
          (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)) :=
    LocalNativeBallOriginalSplit.original_split_pullback m P v₀ b hr hη
  simp only [Category.assoc] at he
  rw [hs] at he
  rw [original_ambient]
  exact he

theorem original_class_eq_tested (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (original m P v₀ b hρ hρr hr hη hr8 hη8) (original_closed m P v₀ b hρ hρr hr hη hr8 hη8) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (LocalNativeCapRelative.tested m P v₀ b hρ hρr hη (by linarith))
      (LocalNativeCapRelative.tested_closed m P v₀ b hρ hρr hη (by linarith)) := by
  apply SupportedSmallCochainComparison.relative_class_eq_positive
    (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
      (LocalNativeBallCut.near P v₀ b r)) _
    (SupportedCap.cover_open _ _ _ (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r))
    (SupportedCap.cover_univ _ _ _ (LocalNativeSupportedCap.cover P v₀ b hρr)) _ (by omega)
  rw [LocalNativeCapRelative.tested_ambient]
  exact small_cochain_eq m P v₀ b hρ hρr hr hη hr8 hη8

theorem original_class_eq_reduced (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (original m P v₀ b hρ hρr hr hη hr8 hη8) (original_closed m P v₀ b hρ hρr hr hη hr8 hη8) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (LocalNativeCapRelative.reduced m P v₀ b hρ hρr hη (by linarith))
      (LocalNativeCapRelative.reduced_closed m P v₀ b hρ hρr hη (by linarith)) :=
  (original_class_eq_tested m P v₀ b hρ hρr hr hη hr8 hη8).trans
    (LocalNativeCapRelative.class_eq m hm P v₀ b hρ hρr hη (by linarith))

end
end Finsler.LocalNativeOriginalCapComparison
