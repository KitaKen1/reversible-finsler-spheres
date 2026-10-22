module

public import Finsler.Loop.StraightenedWrappedOriginalComparison
public import Finsler.Loop.NativeGraphPointSwapClass

/-! Identify the ACTUALLY descended original straightened complementary
support class by its genuine ball-patch restriction. Adjacent branches
are the SAME explicit GLOBAL graph cap class; nonadjacent branch is0.
Exact original cochains, same radii, real small-chain comparison and
relative-support excision are retained. This is a full cap CLASS identity. -/
@[expose] public section
namespace Finsler.StraightenedWrappedGraphIdentification
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem original_class_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (LocalNativeOriginalCapComparison.toNativePair P v₀) ((m + 1) + (m + (m + 1)))).hom
      (StraightenedWrappedOriginalComparison.straightSupportClass m P v₀ b hρ hρr hr hη hr8 hη8) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (StraightenedWrappedOriginalComparison.original m P v₀ b hρ hρr hr hη hr8 hη8)
      (StraightenedWrappedOriginalComparison.original_closed m P v₀ b hρ hρr hr hη hr8 hη8) :=
  CochainClass.classOf_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
      (LocalNativeOriginalCapComparison.toNativePair P v₀)) _ _
    (StraightenedWrappedOriginalComparison.straightened_closed m P v₀ b hρ hρr hr hη hr8 hη8)
    (StraightenedWrappedOriginalComparison.original_closed m P v₀ b hρ hρr hr hη hr8 hη8)

theorem graph_local_reduced (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (NativeBallSupportPatch.inclusion P v₀) ((m + 1) + (m + (m + 1)))).hom
      (NativeQuarterGraphDescent.graphSupportClass P v₀ _
        (StraightenedWrappedOriginalComparison.straightSupportClass m P v₀ b hρ hρr hr hη hr8 hη8)) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (StraightenedWrappedCapRelative.reduced m P v₀ b hρ hρr hη (by linarith))
      (StraightenedWrappedCapRelative.reduced_closed m P v₀ b hρ hρr hη (by linarith)) := by
  let N := (m + 1) + (m + (m + 1))
  let a := StraightenedWrappedOriginalComparison.straightSupportClass m P v₀ b hρ hρr hr hη hr8 hη8
  have he := congrArg (fun f => (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f N).hom
    (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) (NativeGraphLocalCapReduction.local_square P v₀)
  rw [TopPair.singularCohomologyMap_comp] at he
  change (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (LocalNativeOriginalCapComparison.toNativePair P v₀) N).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (NativeQuarterGraphDescent.supportMap P v₀) N).hom
          (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) = _ at he
  rw [NativeQuarterGraphDescent.support_pullback] at he
  exact he.symm.trans ((original_class_pullback m P v₀ b hρ hρr hr hη hr8 hη8).trans
    (StraightenedWrappedOriginalComparison.original_class_eq_reduced m hm P v₀ b hρ hρr hr hη hr8 hη8))

theorem split_pullback_reduced (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {η : ℝ} (hη : 0 < η) :
    cochainPullback (LocalNativeBallCut.toGraph P v₀) (m + (m + 1)) (NativeExplicitGraphCap.split m P v₀ hη) =
      cochainCup m (m + 1) (StraightenedWrappedBallPrimitive.reducedCocycle m P v₀ b)
        (StraightenedWrappedBallCupCorrection.evaluationCocycle m P v₀ hη) := by
  have hr : StraightenedWrappedBallPrimitive.reducedCocycle m P v₀ b = LocalNativeBallPrimitive.reducedCocycle m P v₀ 1 := ite_eq_right hb
  exact (NativeExplicitGraphRestriction.split_pullback m P v₀ hη).trans
    (congrArg (fun c => cochainCup m (m + 1) c (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)) hr.symm)

theorem small_cochain_eq (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
        (LocalNativeBallCut.near P v₀ b r))).f ((m + 1) + (m + (m + 1))) ≫
      cochainPullback (LocalNativeBallCut.toGraph P v₀) _ (NativeExplicitGraphCap.cochain m P v₀ hρ hρr hη) =
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
        (LocalNativeBallCut.near P v₀ b r))).f ((m + 1) + (m + (m + 1))) ≫
      StraightenedWrappedCapCorrection.reducedCochain m P v₀ b hρ hρr hη := by
  let X := LocalNativeBallCut.space P v₀
  let f := LocalNativeBallCut.toGraph P v₀
  let A := LocalNativeSupportedCap.exterior P v₀ b ρ
  let B := LocalNativeBallCut.near P v₀ b r
  let C := NativeExplicitGraphCap.exterior P ρ
  let D := NativeExplicitGraphCap.near P r
  let φ := NormalizedSphereGraphCap.cocycle (m + 1) (by omega)
    (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ
  let hs := NormalizedSphereGraphCap.cocycle_supported (m + 1) (by omega)
    (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ
  have hn := SupportedCapSmallNaturality.naturality f A B C D
    (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r)
    (LocalNativeSupportedCap.cover P v₀ b hρr) (NormalizedSphereGraphCap.exterior_open _ _ _ ρ)
    (NormalizedSphereGraphCap.neighborhood_open _ _ _ r) (NormalizedSphereGraphCap.cover _ _ _ hρr)
    (NativeExplicitGraphRestriction.maps_exterior P v₀ b ρ) (NativeExplicitGraphRestriction.maps_near P v₀ b r)
    (m + 1) (m + (m + 1)) φ hs
  have hc := SupportedCapRepresentative.cut_congr X A B
    (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r)
    (LocalNativeSupportedCap.cover P v₀ b hρr) (m + 1) (m + (m + 1)) ((m + 1) + (m + (m + 1))) rfl
    (cochainPullback f (m + 1) φ) (LocalNativeSupportedCap.cocycle (m + 1) (by omega) P v₀ b hρ)
    (pullback_support f A C (NativeExplicitGraphRestriction.maps_exterior P v₀ b ρ) _ φ hs)
    (LocalNativeSupportedCap.cocycle_supported (m + 1) (by omega) P v₀ b hρ)
    (NativeExplicitGraphRestriction.cocycle_pullback m P v₀ b hρ)
  have he := congrArg (fun a => a ≫ cochainPullback (NativeExplicitGraphCap.nearInclusion P r)
    (m + (m + 1)) (NativeExplicitGraphCap.split m P v₀ hη)) hn
  have hsplit : (push (restriction f B D (NativeExplicitGraphRestriction.maps_near P v₀ b r))).f (m + (m + 1)) ≫
      cochainPullback (NativeExplicitGraphCap.nearInclusion P r) (m + (m + 1)) (NativeExplicitGraphCap.split m P v₀ hη) =
    cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) (m + (m + 1))
      (cochainCup m (m + 1) (StraightenedWrappedBallPrimitive.reducedCocycle m P v₀ b)
        (StraightenedWrappedBallCupCorrection.evaluationCocycle m P v₀ hη)) := by
    change cochainPullback (restriction f B D (NativeExplicitGraphRestriction.maps_near P v₀ b r)) _
      (cochainPullback (SupportedCap.subspaceMap (graphSpace P) D) _ _) = _
    rw [← pullback_comp, restriction_inclusion, pullback_comp, split_pullback_reduced m P v₀ b hb hη]
  simp only [Category.assoc] at he
  rw [hc, hsplit] at he
  exact he

theorem local_class_eq_reduced (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (NativeExplicitGraphIdentification.localRelative m P v₀ hρ hρr hη hηr)
      (NativeExplicitGraphIdentification.local_closed m P v₀ hρ hρr hη hηr) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (StraightenedWrappedCapRelative.reduced m P v₀ b hρ hρr hη hηr)
      (StraightenedWrappedCapRelative.reduced_closed m P v₀ b hρ hρr hη hηr) := by
  apply SupportedSmallCochainComparison.relative_class_eq_positive
    (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
      (LocalNativeBallCut.near P v₀ b r)) _
    (SupportedCap.cover_open _ _ _ (LocalNativeSupportedCap.exterior_open P v₀ b ρ) (LocalNativeSupportedCap.near_open P v₀ b r))
    (SupportedCap.cover_univ _ _ _ (LocalNativeSupportedCap.cover P v₀ b hρr)) _ (by omega)
  rw [NativeExplicitGraphIdentification.local_ambient, StraightenedWrappedCapRelative.reduced_ambient]
  exact small_cochain_eq m P v₀ b hb hρ hρr hη

theorem support_class_adjacent (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeQuarterGraphDescent.graphSupportClass P v₀ _
      (StraightenedWrappedOriginalComparison.straightSupportClass m P v₀ b hρ hρr hr hη hr8 hη8) =
      NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη (by linarith) := by
  apply (NativeBallSupportPatch.cohomologyEquiv P v₀ ((m + 1) + (m + (m + 1)))).injective
  rw [NativeBallSupportPatch.cohomologyEquiv_apply, NativeBallSupportPatch.cohomologyEquiv_apply,
    graph_local_reduced m hm P v₀ b hρ hρr hr hη hr8 hη8]
  have he := CochainClass.classOf_map (RelativeCup.cx (NativeQuarterGraphDescent.graphSupportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeBallSupportPatch.inclusion P v₀)) _ _
    (NativeExplicitGraphCap.relative_closed m P v₀ hρ hρr hη (by linarith))
    (NativeExplicitGraphIdentification.local_closed m P v₀ hρ hρr hη (by linarith))
  exact (local_class_eq_reduced m P v₀ b hb hρ hρr hη (by linarith)).symm.trans he.symm

theorem reduced_nonadjacent_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    StraightenedWrappedCapRelative.reduced m P v₀ 1 hρ hρr hη hηr = 0 := by
  apply RelativeCupCochain.toAmbient_injective (NativeBallSupportPatch.localPair P v₀) _
  rw [StraightenedWrappedCapRelative.reduced_ambient, map_zero]
  have he : StraightenedWrappedBallPrimitive.reducedCocycle m P v₀ 1 = 0 := ite_eq_left rfl
  dsimp only [StraightenedWrappedCapCorrection.reducedCochain]
  rw [he, cochainCup_zero_left]
  change (LocalNativeSupportedCap.operation (m + 1) (by omega) P v₀ 1 hρ hρr).component (m + (m + 1)) ≫
    ((push (LocalNativeBallOriginalSplit.nearInclusion P v₀ 1 r)).f (m + (m + 1)) ≫ 0) = 0
  rw [comp_zero, comp_zero]

theorem support_class_nonadjacent_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeQuarterGraphDescent.graphSupportClass P v₀ _
      (StraightenedWrappedOriginalComparison.straightSupportClass m P v₀ 1 hρ hρr hr hη hr8 hη8) = 0 := by
  apply (NativeBallSupportPatch.cohomologyEquiv P v₀ ((m + 1) + (m + (m + 1)))).injective
  rw [NativeBallSupportPatch.cohomologyEquiv_apply, map_zero, graph_local_reduced m hm P v₀ 1 hρ hρr hr hη hr8 hη8]
  have he := reduced_nonadjacent_zero m P v₀ hρ hρr hη (show η + r ≤ (1 / 4 : ℝ) by linarith)
  have hz : RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) ((m + 1) + (m + (m + 1))) 0 = 0 := map_zero _
  exact (CochainClass.classOf_congr _ _ he _ hz).trans (CochainClass.classOf_zero _ _ hz)

end
end Finsler.StraightenedWrappedGraphIdentification
