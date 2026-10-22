module

public import Finsler.Loop.NativeExplicitGraphRestriction

/-! Identify the ACTUALLY descended ORIGINAL nonadjacent graph class
with the explicit GLOBAL normalized graph cap. Exact small-chain
naturality, real support-prism correction and actual ball excision
injectivity retain the SAME original class and all original radii. -/
@[expose] public section
namespace Finsler.NativeExplicitGraphIdentification
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem small_cochain_eq (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ 1 ρ)
        (LocalNativeBallCut.near P v₀ 1 r))).f ((m + 1) + (m + (m + 1))) ≫
      cochainPullback (LocalNativeBallCut.toGraph P v₀) _ (NativeExplicitGraphCap.cochain m P v₀ hρ hρr hη) =
    (SmallChainCarrier.inclusion (LocalNativeBallCut.space P v₀)
      (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ 1 ρ)
        (LocalNativeBallCut.near P v₀ 1 r))).f ((m + 1) + (m + (m + 1))) ≫
      LocalNativeCapCorrection.reducedCochain m P v₀ 1 hρ hρr hη := by
  let X := LocalNativeBallCut.space P v₀
  let f := LocalNativeBallCut.toGraph P v₀
  let A := LocalNativeSupportedCap.exterior P v₀ 1 ρ
  let B := LocalNativeBallCut.near P v₀ 1 r
  let C := NativeExplicitGraphCap.exterior P ρ
  let D := NativeExplicitGraphCap.near P r
  let φ := NormalizedSphereGraphCap.cocycle (m + 1) (by omega)
    (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ
  let hs := NormalizedSphereGraphCap.cocycle_supported (m + 1) (by omega)
    (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ
  have hn := SupportedCapSmallNaturality.naturality f A B C D
    (LocalNativeSupportedCap.exterior_open P v₀ 1 ρ) (LocalNativeSupportedCap.near_open P v₀ 1 r)
    (LocalNativeSupportedCap.cover P v₀ 1 hρr) (NormalizedSphereGraphCap.exterior_open _ _ _ ρ)
    (NormalizedSphereGraphCap.neighborhood_open _ _ _ r) (NormalizedSphereGraphCap.cover _ _ _ hρr)
    (NativeExplicitGraphRestriction.maps_exterior P v₀ 1 ρ) (NativeExplicitGraphRestriction.maps_near P v₀ 1 r)
    (m + 1) (m + (m + 1)) φ hs
  have hc := SupportedCapRepresentative.cut_congr X A B
    (LocalNativeSupportedCap.exterior_open P v₀ 1 ρ) (LocalNativeSupportedCap.near_open P v₀ 1 r)
    (LocalNativeSupportedCap.cover P v₀ 1 hρr) (m + 1) (m + (m + 1)) ((m + 1) + (m + (m + 1))) rfl
    (cochainPullback f (m + 1) φ) (LocalNativeSupportedCap.cocycle (m + 1) (by omega) P v₀ 1 hρ)
    (pullback_support f A C (NativeExplicitGraphRestriction.maps_exterior P v₀ 1 ρ) _ φ hs)
    (LocalNativeSupportedCap.cocycle_supported (m + 1) (by omega) P v₀ 1 hρ)
    (NativeExplicitGraphRestriction.cocycle_pullback m P v₀ 1 hρ)
  have he := congrArg (fun a => a ≫ cochainPullback (NativeExplicitGraphCap.nearInclusion P r)
    (m + (m + 1)) (NativeExplicitGraphCap.split m P v₀ hη)) hn
  have hsplit : (push (restriction f B D (NativeExplicitGraphRestriction.maps_near P v₀ 1 r))).f (m + (m + 1)) ≫
      cochainPullback (NativeExplicitGraphCap.nearInclusion P r) (m + (m + 1)) (NativeExplicitGraphCap.split m P v₀ hη) =
    cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ 1 r) (m + (m + 1))
      (cochainCup m (m + 1) (LocalNativeBallPrimitive.reducedCocycle m P v₀ 1)
        (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)) := by
    change cochainPullback (restriction f B D (NativeExplicitGraphRestriction.maps_near P v₀ 1 r)) _
      (cochainPullback (SupportedCap.subspaceMap (graphSpace P) D) _ _) = _
    rw [← pullback_comp, restriction_inclusion, pullback_comp, NativeExplicitGraphRestriction.split_pullback]
  simp only [Category.assoc] at he
  rw [hc, hsplit] at he
  exact he

def localRelative (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :=
  RelativeCupCochain.pullback (NativeBallSupportPatch.inclusion P v₀) _
    (NativeExplicitGraphCap.relativeCocycle m P v₀ hρ hρr hη hηr)

theorem local_ambient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.toAmbient (NativeBallSupportPatch.localPair P v₀) _ (localRelative m P v₀ hρ hρr hη hηr) =
      cochainPullback (LocalNativeBallCut.toGraph P v₀) _ (NativeExplicitGraphCap.cochain m P v₀ hρ hρr hη) := by
  rw [localRelative, RelativeCupCochain.toAmbient_pullback, NativeExplicitGraphCap.relative_ambient]
  have hf : TopPair.Hom.fst (NativeBallSupportPatch.inclusion P v₀) = LocalNativeBallCut.toGraph P v₀ := by
    apply TopCat.ext
    intro z
    exact TopPair.ofSubsetMap_fst_apply (LocalNativeBallCut.toGraph P v₀) (NativeBallSupportPatch.maps_support P v₀) z
  rw [hf]

theorem local_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) _ (localRelative m P v₀ hρ hρr hη hηr) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (NativeQuarterGraphDescent.graphSupportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeBallSupportPatch.inclusion P v₀)) _ _
    (NativeExplicitGraphCap.relative_closed m P v₀ hρ hρr hη hηr)

theorem local_class_eq_reduced (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (localRelative m P v₀ hρ hρr hη hηr) (local_closed m P v₀ hρ hρr hη hηr) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (LocalNativeCapRelative.reduced m P v₀ 1 hρ hρr hη hηr) (LocalNativeCapRelative.reduced_closed m P v₀ 1 hρ hρr hη hηr) := by
  apply SupportedSmallCochainComparison.relative_class_eq_positive
    (SupportedCap.cover (LocalNativeBallCut.space P v₀) (LocalNativeSupportedCap.exterior P v₀ 1 ρ)
      (LocalNativeBallCut.near P v₀ 1 r)) _
    (SupportedCap.cover_open _ _ _ (LocalNativeSupportedCap.exterior_open P v₀ 1 ρ) (LocalNativeSupportedCap.near_open P v₀ 1 r))
    (SupportedCap.cover_univ _ _ _ (LocalNativeSupportedCap.cover P v₀ 1 hρr)) _ (by omega)
  rw [local_ambient, LocalNativeCapRelative.reduced_ambient]
  exact small_cochain_eq m P v₀ hρ hρr hη

theorem support_class_eq (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeQuarterGraphDescent.graphSupportClass P v₀ _
      (NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ 1 hρ hρr hr hη hr8 hη8) =
    NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη (by linarith) := by
  apply (NativeBallSupportPatch.cohomologyEquiv P v₀ ((m + 1) + (m + (m + 1)))).injective
  rw [NativeBallSupportPatch.cohomologyEquiv_apply, NativeBallSupportPatch.cohomologyEquiv_apply,
    NativeGraphLocalCapReduction.graph_local_reduced m hm P v₀ 1 hρ hρr hr hη hr8 hη8]
  have he := CochainClass.classOf_map (RelativeCup.cx (NativeQuarterGraphDescent.graphSupportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeBallSupportPatch.inclusion P v₀)) _ _
    (NativeExplicitGraphCap.relative_closed m P v₀ hρ hρr hη (by linarith)) (local_closed m P v₀ hρ hρr hη (by linarith))
  exact (local_class_eq_reduced m P v₀ hρ hρr hη (by linarith)).symm.trans he.symm

end
end Finsler.NativeExplicitGraphIdentification
