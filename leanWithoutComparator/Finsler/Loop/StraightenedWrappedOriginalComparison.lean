module

public import Finsler.Loop.StraightenedWrappedCapRelative
public import Finsler.Loop.NativeWrappedQuarterSupport
public import Finsler.Loop.LocalNativeOriginalCapComparison

/-! Connect the SAME original complementary-cut cochain to the ACTUAL
straightened supported cap, through exact small-chain naturality and
the genuine support-preserving correction. No symmetry of the chosen
Thom cochain or subdivision retraction is assumed. -/
@[expose] public section
namespace Finsler.StraightenedWrappedOriginalComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeMeridianPairCoordinates Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def straightenedRelative (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  RelativeCupCochain.pullback (NativeWrappedQuarterSupport.nativePairSwap P v₀) ((m + 1) + (m + (m + 1)))
    (NativeWrappedQuarterSupport.relativeCocycle m m P v₀ b hρ hρr hr hη hr8 hη8
      (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)))

theorem straightened_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.differential (NativeQuarterSupport.supportPair P v₀) _
      (straightenedRelative m P v₀ b hρ hρr hr hη hr8 hη8) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeWrappedQuarterSupport.nativePairSwap P v₀)) _ _
    (NativeWrappedQuarterSupport.relative_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))

def straightSupportClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  CochainClass.classOf (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀)) _
    (straightenedRelative m P v₀ b hρ hρr hr hη hr8 hη8) (straightened_closed m P v₀ b hρ hρr hr hη hr8 hη8)

theorem straightSupportClass_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeWrappedQuarterSupport.nativePairSwap P v₀)
      ((m + 1) + (m + (m + 1)))).hom (NativeWrappedQuarterSupport.supportClass m P v₀ b hρ hρr hr hη hr8 hη8) =
      straightSupportClass m P v₀ b hρ hρr hr hη hr8 hη8 :=
  CochainClass.classOf_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeWrappedQuarterSupport.nativePairSwap P v₀)) _ _
    (NativeWrappedQuarterSupport.relative_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))
    (straightened_closed m P v₀ b hρ hρr hr hη hr8 hη8)

theorem local_cut_square {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.toNative P v₀ ≫ (NativeCutPointSwap.nativeSwap P ≫ NativeWrappedQuarterSupport.intoCut P v₀ b) =
      NativeCutPointSwap.straightenedCut P v₀ b := by
  have h := congrArg (fun f => f ≫ NativeWrappedQuarterSupport.intoCut P v₀ b) (NativeCutPointSwap.ball_native_square P v₀)
  exact (Category.assoc _ _ _).symm.trans (h.symm.trans (Category.assoc _ _ _))

def original (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  RelativeCupCochain.pullback (LocalNativeOriginalCapComparison.toNativePair P v₀) ((m + 1) + (m + (m + 1)))
    (straightenedRelative m P v₀ b hρ hρr hr hη hr8 hη8)

theorem original_ambient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (original m P v₀ b hρ hρr hr hη hr8 hη8) =
      cochainPullback (NativeCutPointSwap.straightenedCut P v₀ b) ((m + 1) + (m + (m + 1)))
        (LocalizedParameterCutCochain.cochain m m (LocalNativeBallCut.center P v₀) hρ hρr hr hη
          (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))) := by
  rw [original, RelativeCupCochain.toAmbient_pullback, LocalNativeOriginalCapComparison.toNativePair_fst,
    straightenedRelative, RelativeCupCochain.toAmbient_pullback, NativeWrappedQuarterSupport.nativePairSwap_fst,
    NativeWrappedQuarterSupport.relative_ambient, NativeWrappedQuarterSupport.cochain,
    ← pullback_comp, ← pullback_comp]
  exact congrArg (fun f => cochainPullback f ((m + 1) + (m + (m + 1)))
    (LocalizedParameterCutCochain.cochain m m (LocalNativeBallCut.center P v₀) hρ hρr hr hη
      (classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m))))
    ((Category.assoc (LocalNativeBallCut.toNative P v₀) (NativeCutPointSwap.nativeSwap P)
      (NativeWrappedQuarterSupport.intoCut P v₀ b)).trans (local_cut_square P v₀ b))

theorem original_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) _ (original m P v₀ b hρ hρr hr hη hr8 hη8) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (LocalNativeOriginalCapComparison.toNativePair P v₀)) _ _
    (straightened_closed m P v₀ b hρ hρr hr hη hr8 hη8)

theorem small_cochain_eq (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
        (LocalNativeBallCut.near P v₀ b r))).f ((m + 1) + (m + (m + 1))) ≫
      RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (original m P v₀ b hρ hρr hr hη hr8 hη8) =
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
        (LocalNativeBallCut.near P v₀ b r))).f ((m + 1) + (m + (m + 1))) ≫
      StraightenedWrappedCapCorrection.testedCochain m P v₀ b hρ hρr hη := by
  let X := LocalNativeBallCut.space P v₀
  let Y := SelfCutThomCocycle.parameters (m + 1)
  let f := NativeCutPointSwap.straightenedCut P v₀ b
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
    (StraightenedWrappedBallSplit.maps_exterior P v₀ b ρ) (StraightenedWrappedBallSplit.maps_near P v₀ b r) (m + 1) (m + (m + 1)) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
  have hc := SupportedCapRepresentative.cut_congr X A B
    (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r)
    (LocalNativeSupportedCap.cover P v₀ b hρr) (m + 1) (m + (m + 1)) ((m + 1) + (m + (m + 1))) rfl
    (cochainPullback f (m + 1) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ))
    (LocalNativeSupportedCap.cocycle (m + 1) (by omega) P v₀ b hρ)
    (pullback_support f A C (StraightenedWrappedBallSplit.maps_exterior P v₀ b ρ) _
      (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ))
    (LocalNativeSupportedCap.cocycle_supported (m + 1) (by omega) P v₀ b hρ)
    (NativeCutPointSwap.straightened_cocycle (m + 1) (by omega) P v₀ b hρ)
  have he := congrArg (fun a => a ≫ split) hn
  have hs : (push (restriction f B D (StraightenedWrappedBallSplit.maps_near P v₀ b r))).f (m + (m + 1)) ≫ split =
      cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) (m + (m + 1))
        (cochainCup m (m + 1) (StraightenedWrappedBallPrimitive.testedCocycle m P v₀ b)
          (StraightenedWrappedBallCupCorrection.evaluationCocycle m P v₀ hη)) :=
    StraightenedWrappedBallSplit.original_split_pullback m P v₀ b hr hη
  simp only [Category.assoc] at he
  rw [hc, hs] at he
  rw [original_ambient]
  exact he

theorem original_class_eq_tested (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (original m P v₀ b hρ hρr hr hη hr8 hη8) (original_closed m P v₀ b hρ hρr hr hη hr8 hη8) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (StraightenedWrappedCapRelative.tested m P v₀ b hρ hρr hη (by linarith))
      (StraightenedWrappedCapRelative.tested_closed m P v₀ b hρ hρr hη (by linarith)) := by
  apply SupportedSmallCochainComparison.relative_class_eq_positive
    (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
      (LocalNativeBallCut.near P v₀ b r)) _
    (SupportedCap.cover_open _ _ _ (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r))
    (SupportedCap.cover_univ _ _ _ (LocalNativeSupportedCap.cover P v₀ b hρr)) _ (by omega)
  rw [StraightenedWrappedCapRelative.tested_ambient]
  exact small_cochain_eq m P v₀ b hρ hρr hr hη hr8 hη8

theorem original_class_eq_reduced (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (original m P v₀ b hρ hρr hr hη hr8 hη8) (original_closed m P v₀ b hρ hρr hr hη hr8 hη8) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (StraightenedWrappedCapRelative.reduced m P v₀ b hρ hρr hη (by linarith))
      (StraightenedWrappedCapRelative.reduced_closed m P v₀ b hρ hρr hη (by linarith)) :=
  (original_class_eq_tested m P v₀ b hρ hρr hr hη hr8 hη8).trans
    (StraightenedWrappedCapRelative.class_eq m hm P v₀ b hρ hρr hη (by linarith))

end
end Finsler.StraightenedWrappedOriginalComparison
