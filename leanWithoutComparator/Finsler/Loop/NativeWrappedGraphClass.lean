module

public import Finsler.Loop.StraightenedWrappedGraphIdentification
public import Finsler.Loop.NativePointSwapPairs

/-! Recover the SAME ORIGINAL wrapped support class from its proved
straightened class by actual involutive maps of pairs. The actual
descended wrapped graph class is the exchanged explicit graph cap on
adjacent branches and0 on the nonadjacent branch. No coefficient is assigned. -/
@[expose] public section
namespace Finsler.NativeWrappedGraphClass
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem support_class_adjacent (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeQuarterGraphDescent.graphSupportClass P v₀ _
      (NativeWrappedQuarterSupport.supportClass m P v₀ b hρ hρr hr hη hr8 hη8) =
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeCutPointSwap.graphPairSwap P v₀)
      ((m + 1) + (m + (m + 1)))).hom (NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη (by linarith)) := by
  let N := (m + 1) + (m + (m + 1))
  let a := NativeWrappedQuarterSupport.supportClass m P v₀ b hρ hρr hr hη hr8 hη8
  let s := NativeWrappedQuarterSupport.nativePairSwap P v₀
  let G := NativeQuarterGraphDescent.supportMap P v₀
  let c := NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη (show η + r ≤ (1 / 4 : ℝ) by linarith)
  have hgraph := StraightenedWrappedGraphIdentification.support_class_adjacent m hm P v₀ b hb hρ hρr hr hη hr8 hη8
  have h₀ : (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) s N).hom a =
      (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) G N).hom c :=
    (StraightenedWrappedOriginalComparison.straightSupportClass_pullback m P v₀ b hρ hρr hr hη hr8 hη8).trans
      ((NativeQuarterGraphDescent.support_pullback P v₀ N
        (StraightenedWrappedOriginalComparison.straightSupportClass m P v₀ b hρ hρr hr hη hr8 hη8)).symm.trans
        (congrArg (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) G N).hom hgraph))
  have hx := congrArg (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) s N).hom h₀
  have hi := NativePointSwapPairs.cohomology_involution (NativeQuarterSupport.supportPair P v₀) s
    (NativePointSwapPairs.nativePairSwap_involution P v₀) N a
  have hv := hi.symm.trans (hx.trans (NativePointSwapPairs.support_pullback_exchange P v₀ N c).symm)
  apply (NativeQuarterGraphDescent.supportEquiv P v₀ N).injective
  rw [NativeQuarterGraphDescent.supportEquiv_apply, NativeQuarterGraphDescent.supportEquiv_apply,
    NativeQuarterGraphDescent.support_pullback]
  exact hv

theorem support_class_nonadjacent_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeQuarterGraphDescent.graphSupportClass P v₀ _
      (NativeWrappedQuarterSupport.supportClass m P v₀ 1 hρ hρr hr hη hr8 hη8) = 0 := by
  let N := (m + 1) + (m + (m + 1))
  let a := NativeWrappedQuarterSupport.supportClass m P v₀ 1 hρ hρr hr hη hr8 hη8
  let s := NativeWrappedQuarterSupport.nativePairSwap P v₀
  let G := NativeQuarterGraphDescent.supportMap P v₀
  have hg := StraightenedWrappedGraphIdentification.support_class_nonadjacent_zero m hm P v₀ hρ hρr hr hη hr8 hη8
  have hstraight : StraightenedWrappedOriginalComparison.straightSupportClass m P v₀ 1 hρ hρr hr hη hr8 hη8 = 0 :=
    (NativeQuarterGraphDescent.support_pullback P v₀ N _).symm.trans
      ((congrArg (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) G N).hom hg).trans (map_zero _))
  have hs := (StraightenedWrappedOriginalComparison.straightSupportClass_pullback m P v₀ 1 hρ hρr hr hη hr8 hη8).trans hstraight
  have hx := congrArg (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) s N).hom hs
  have hi := NativePointSwapPairs.cohomology_involution (NativeQuarterSupport.supportPair P v₀) s
    (NativePointSwapPairs.nativePairSwap_involution P v₀) N a
  have hv : a = 0 := hi.symm.trans (hx.trans (map_zero _))
  change (NativeQuarterGraphDescent.supportEquiv P v₀ N).symm a = 0
  rw [hv, map_zero]

def boundaryClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  NativeQuarterGraphDescent.graphClass P v₀ ((m + 1) + (m + (m + 1)))
    (NativeWrappedQuarterSupport.supportClass m P v₀ b hρ hρr hr hη hr8 hη8)

theorem boundary_absolute {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : (NativeQuarterGraphDescent.graphSupportPair P v₀).singularCohomology coeff (ZMod 2) coeff q) :
    (relativeToPool (graphPair P v₀) q).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) q).hom a) =
      (relativeToPool (NativeQuarterGraphDescent.graphSupportPair P v₀) q).hom a := by
  have he := ConcreteCategory.congr_hom
    (relative_to_absolute_natural (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) q) a
  have hf : TopPair.Hom.fst (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) = 𝟙 (graphSpace P) := by
    apply TopCat.ext
    intro z
    exact TopPair.ofSubsetMap_fst_apply (𝟙 (graphSpace P)) (NativeQuarterGraphDescent.graphBoundary_outside P v₀) z
  change (relativeToPool (graphPair P v₀) q).hom
    ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) q).hom a) =
    (cohPullback (TopPair.Hom.fst (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀)) q).hom
      ((relativeToPool (NativeQuarterGraphDescent.graphSupportPair P v₀) q).hom a) at he
  rw [hf] at he
  exact he.trans (ConcreteCategory.congr_hom ((singularCohomologyZMod2 q).map_id (Opposite.op (graphSpace P))) _)

theorem support_swap_absolute (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    (relativeToPool (NativeQuarterGraphDescent.graphSupportPair P v₀) ((m + 1) + (m + (m + 1)))).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeCutPointSwap.graphPairSwap P v₀)
        ((m + 1) + (m + (m + 1)))).hom (NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη hηr)) =
    (cohPullback (NativeCutPointSwap.graphSwap P) ((m + 1) + (m + (m + 1)))).hom (NativeExplicitGraphClass.explicitClass m P v₀) := by
  have he := ConcreteCategory.congr_hom (relative_to_absolute_natural (NativeCutPointSwap.graphPairSwap P v₀)
    ((m + 1) + (m + (m + 1)))) (NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη hηr)
  change (relativeToPool (NativeQuarterGraphDescent.graphSupportPair P v₀) _).hom
    ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeCutPointSwap.graphPairSwap P v₀) _).hom _) =
    (cohPullback (TopPair.Hom.fst (NativeCutPointSwap.graphPairSwap P v₀)) _).hom _ at he
  rw [NativePointSwapPairs.graphPairSwap_fst] at he
  exact he.trans (congrArg (cohPullback (NativeCutPointSwap.graphSwap P) _).hom
    (NativeExplicitGraphClass.support_absolute m P v₀ hρ hρr hη hηr))

theorem absolute_uncast_adjacent (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (relativeToPool (graphPair P v₀) ((m + 1) + (m + (m + 1)))).hom (boundaryClass m P v₀ b hρ hρr hr hη hr8 hη8) =
      (cohPullback (NativeCutPointSwap.graphSwap P) ((m + 1) + (m + (m + 1)))).hom (NativeExplicitGraphClass.explicitClass m P v₀) := by
  unfold boundaryClass NativeQuarterGraphDescent.graphClass
  rw [support_class_adjacent m hm P v₀ b hb hρ hρr hr hη hr8 hη8]
  exact (boundary_absolute P v₀ _ _).trans (support_swap_absolute m P v₀ hρ hρr hη (by linarith))

theorem boundary_nonadjacent_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    boundaryClass m P v₀ 1 hρ hρr hr hη hr8 hη8 = 0 := by
  unfold boundaryClass NativeQuarterGraphDescent.graphClass
  rw [support_class_nonadjacent_zero m hm P v₀ hρ hρr hr hη hr8 hη8, map_zero]

end
end Finsler.NativeWrappedGraphClass
