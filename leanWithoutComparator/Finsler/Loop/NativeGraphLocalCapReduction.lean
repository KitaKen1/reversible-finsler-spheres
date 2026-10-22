module

public import Finsler.Loop.LocalNativeOriginalCapComparison
public import Finsler.Loop.NativeGraphBranchPairing

/-! The ACTUALLY descended original graph class is determined by its
real ball-patch restriction, now equal to the reduced supported cap.
In particular the two ADJACENT ORIGINAL branch classes and their
actual double-prism pairings vanish, for the SAME eighth-small radii. -/
@[expose] public section
namespace Finsler.NativeGraphLocalCapReduction
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativeMeridianPairCoordinates Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

private theorem subset_comp {X Y Z : TopCat.{0}} {A : Set X} {B : Set Y} {C : Set Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (hh : Set.MapsTo h A C)
    (he : f ≫ g = h) :
    TopPair.ofSubsetMap f hf ≫ TopPair.ofSubsetMap g hg = TopPair.ofSubsetMap h hh := by
  subst h
  exact (TopPair.ofSubsetMap_comp f g hf hg hh).symm

theorem local_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    LocalNativeOriginalCapComparison.toNativePair P v₀ ≫ NativeQuarterGraphDescent.supportMap P v₀ =
      NativeBallSupportPatch.inclusion P v₀ :=
  subset_comp (LocalNativeBallCut.toNative P v₀) (sphereCoordinates P) (LocalNativeBallCut.toGraph P v₀)
    (LocalNativeOriginalCapComparison.maps_support P v₀) (NativeQuarterGraphPatch.maps_support P v₀)
    (NativeBallSupportPatch.maps_support P v₀) (LocalNativeBallCut.coordinates P v₀)

theorem original_class_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (LocalNativeOriginalCapComparison.toNativePair P v₀) ((m + 1) + (m + (m + 1)))).hom
      (NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (LocalNativeOriginalCapComparison.original m P v₀ b hρ hρr hr hη hr8 hη8)
      (LocalNativeOriginalCapComparison.original_closed m P v₀ b hρ hρr hr hη hr8 hη8) :=
  CochainClass.classOf_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff)
      (LocalNativeOriginalCapComparison.toNativePair P v₀)) _ _
    (NativeQuarterSupport.relative_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))
    (LocalNativeOriginalCapComparison.original_closed m P v₀ b hρ hρr hr hη hr8 hη8)

theorem graph_local_reduced (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (NativeBallSupportPatch.inclusion P v₀) ((m + 1) + (m + (m + 1)))).hom
      (NativeQuarterGraphDescent.graphSupportClass P v₀ _
        (NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8)) =
    CochainClass.classOf (RelativeCup.cx (NativeBallSupportPatch.localPair P v₀)) _
      (LocalNativeCapRelative.reduced m P v₀ b hρ hρr hη (by linarith))
      (LocalNativeCapRelative.reduced_closed m P v₀ b hρ hρr hη (by linarith)) := by
  let N := (m + 1) + (m + (m + 1))
  let a := NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8
  have he := congrArg (fun f => (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f N).hom
    (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) (local_square P v₀)
  rw [TopPair.singularCohomologyMap_comp] at he
  change (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (LocalNativeOriginalCapComparison.toNativePair P v₀) N).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (NativeQuarterGraphDescent.supportMap P v₀) N).hom
          (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) = _ at he
  rw [NativeQuarterGraphDescent.support_pullback] at he
  exact he.symm.trans ((original_class_pullback m P v₀ b hρ hρr hr hη hr8 hη8).trans
    (LocalNativeOriginalCapComparison.original_class_eq_reduced m hm P v₀ b hρ hρr hr hη hr8 hη8))

theorem reduced_relative_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    LocalNativeCapRelative.reduced m P v₀ b hρ hρr hη hηr = 0 := by
  apply RelativeCupCochain.toAmbient_injective (NativeBallSupportPatch.localPair P v₀) _
  rw [LocalNativeCapRelative.reduced_ambient, map_zero]
  have he : LocalNativeBallPrimitive.reducedCocycle m P v₀ b = 0 := ite_eq_right hb
  dsimp only [LocalNativeCapCorrection.reducedCochain]
  rw [he, cochainCup_zero_left]
  change (LocalNativeSupportedCap.operation (m + 1) (by omega) P v₀ b hρ hρr).component (m + (m + 1)) ≫
    ((Finsler.SupportedCapNaturality.push (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r)).f (m + (m + 1)) ≫ 0) = 0
  rw [comp_zero, comp_zero]

theorem graph_support_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeQuarterGraphDescent.graphSupportClass P v₀ _
      (NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8) = 0 := by
  apply (NativeBallSupportPatch.cohomologyEquiv P v₀ ((m + 1) + (m + (m + 1)))).injective
  rw [NativeBallSupportPatch.cohomologyEquiv_apply, graph_local_reduced m hm P v₀ b hρ hρr hr hη hr8 hη8,
    map_zero]
  have hz : RelativeCupCochain.differential (NativeBallSupportPatch.localPair P v₀) ((m + 1) + (m + (m + 1))) 0 = 0 := map_zero _
  exact (CochainClass.classOf_congr _ _ (reduced_relative_zero m P v₀ b hb hρ hρr hη (by linarith)) _ hz).trans
    (CochainClass.classOf_zero _ _ hz)

theorem original_graph_class_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeCutGraphDescent.originalGraphClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) = 0 := by
  have hq : NativeQuarterGraphDescent.originalGraphClass m P v₀ b hρ hρr hr hη hr8 hη8 = 0 := by
    change (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) _).hom _ = 0
    rw [graph_support_zero m hm P v₀ b hb hρ hρr hr hη hr8 hη8, map_zero]
  exact (NativeQuarterGraphCompatibility.original_graph_class_eq m P v₀ b hρ hρr hr hη hr8 hη8).symm.trans hq

theorem original_branchPairing_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativePairDoublePrismSource.branchPairing m hm P v₀ b hρ hρr hr hη (by linarith) (by linarith) = 0 := by
  have he := NativeGraphBranchPairing.original_branchPairing_fundamental m hm P v₀ b hρ hρr hr hη (by linarith) (by linarith)
  have hg := original_graph_class_zero m hm P v₀ b hb hρ hρr hr hη hr8 hη8
  have hp : NativeGraphBranchPairing.primitiveClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) = 0 := by
    unfold NativeGraphBranchPairing.primitiveClass
    rw [hg, map_zero]
  have ha : NativeGraphBranchPairing.absoluteClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) = 0 := by
    unfold NativeGraphBranchPairing.absoluteClass
    rw [hp, map_zero]
  rw [ha, map_zero] at he
  exact he.trans (LinearMap.zero_apply _)

end
end Finsler.NativeGraphLocalCapReduction
