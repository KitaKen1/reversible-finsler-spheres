module

public import Finsler.Loop.NativeQuarterGraphDescent
public import Finsler.Loop.NativeCutGraphDescent

/-! Shrinking the support changes neither the SAME descended graph
class nor its boundary restriction. Actual identity pair maps and
the support-pullback equivalence prove the comparison. -/
@[expose] public section
namespace Finsler.NativeQuarterGraphCompatibility
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates
open Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

private theorem subset_comp {X Y Z : TopCat.{0}} {A : Set X} {B : Set Y} {C : Set Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (hh : Set.MapsTo h A C)
    (he : f ≫ g = h) :
    TopPair.ofSubsetMap f hf ≫ TopPair.ofSubsetMap g hg = TopPair.ofSubsetMap h hh := by
  subst h
  exact (TopPair.ofSubsetMap_comp f g hf hg hh).symm

theorem graph_good_subset_half {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeQuarterGraphPatch.graphGood P v₀ ⊆ NativeNorthSupportPatch.graphGood P v₀ := by
  intro z hz
  exact ⟨lt_trans hz.1 (by norm_num), lt_trans hz.2 (by norm_num)⟩

def graphHalfToQuarter {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeCutGraphDescent.graphSupportPair P v₀ ⟶ NativeQuarterGraphDescent.graphSupportPair P v₀ :=
  TopPair.ofSubsetMap (B := (NativeNorthSupportPatch.graphGood P v₀)ᶜ)
    (B' := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ) (𝟙 (graphSpace P))
    (fun _ hz hg => hz (graph_good_subset_half P v₀ hg))

theorem support_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeQuarterSupport.halfToQuarter P v₀ ≫ NativeQuarterGraphDescent.supportMap P v₀ =
      NativeCutGraphDescent.supportMap P v₀ ≫ graphHalfToQuarter P v₀ := by
  let h : Set.MapsTo (sphereCoordinates P) (NativePairGoodCarrier.good P v₀)ᶜ
      (NativeQuarterGraphPatch.graphGood P v₀)ᶜ := fun _ hz hg => hz (NativeQuarterSupport.good_subset_half P v₀ hg)
  have hl := subset_comp (A := (NativePairGoodCarrier.good P v₀)ᶜ) (B := (NativeQuarterSupport.good P v₀)ᶜ) (C := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ) (𝟙 (parameters P)) (sphereCoordinates P) (sphereCoordinates P)
    (fun _ hz hg => hz (NativeQuarterSupport.good_subset_half P v₀ hg))
    (NativeQuarterGraphPatch.maps_support P v₀) h (Category.id_comp _)
  have hr := subset_comp (A := (NativePairGoodCarrier.good P v₀)ᶜ) (B := (NativeNorthSupportPatch.graphGood P v₀)ᶜ) (C := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ) (sphereCoordinates P) (𝟙 (graphSpace P)) (sphereCoordinates P)
    (NativeNorthSupportPatch.maps_support P v₀)
    (fun _ hz hg => hz (graph_good_subset_half P v₀ hg)) h (Category.comp_id _)
  exact hl.trans hr.symm

theorem support_class_half_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (graphHalfToQuarter P v₀)
      ((m + 1) + (m + (m + 1)))).hom
      (NativeQuarterGraphDescent.graphSupportClass P v₀ _
        (NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8)) =
    NativeCutGraphDescent.graphSupportClass P v₀ _
      (NativePairGoodCarrier.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith)) := by
  let N := (m + 1) + (m + (m + 1))
  let a := NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8
  apply (NativeCutGraphDescent.supportEquiv P v₀ N).injective
  rw [NativeCutGraphDescent.supportEquiv_apply, NativeCutGraphDescent.supportEquiv_apply,
    NativeCutGraphDescent.support_pullback]
  have he := congrArg (fun f => (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f N).hom
    (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) (support_square P v₀)
  rw [TopPair.singularCohomologyMap_comp, TopPair.singularCohomologyMap_comp] at he
  change (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (NativeQuarterSupport.halfToQuarter P v₀) N).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (NativeQuarterGraphDescent.supportMap P v₀) N).hom
          (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) = _ at he
  rw [NativeQuarterGraphDescent.support_pullback] at he
  exact he.symm.trans (NativeQuarterSupport.originalPrimitiveSupportClass_half_pullback m P v₀ b hρ hρr hr hη hr8 hη8)

theorem boundary_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeCutGraphDescent.graphBoundaryToSupport P v₀ ≫ graphHalfToQuarter P v₀ =
      NativeQuarterGraphDescent.graphBoundaryToSupport P v₀ := by
  exact subset_comp (A := graphBoundary P v₀) (B := (NativeNorthSupportPatch.graphGood P v₀)ᶜ) (C := (NativeQuarterGraphPatch.graphGood P v₀)ᶜ) (𝟙 (graphSpace P)) (𝟙 (graphSpace P)) (𝟙 (graphSpace P))
    (NativeCutGraphDescent.graphBoundary_outside P v₀)
    (fun _ hz hg => hz (graph_good_subset_half P v₀ hg))
    (NativeQuarterGraphDescent.graphBoundary_outside P v₀) (Category.id_comp _)

theorem original_graph_class_eq (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeQuarterGraphDescent.originalGraphClass m P v₀ b hρ hρr hr hη hr8 hη8 =
      NativeCutGraphDescent.originalGraphClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) := by
  let N := (m + 1) + (m + (m + 1))
  let a := NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8
  have he := congrArg (fun f => (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f N).hom
    (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) (boundary_square P v₀)
  rw [TopPair.singularCohomologyMap_comp] at he
  change (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (NativeCutGraphDescent.graphBoundaryToSupport P v₀) N).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (graphHalfToQuarter P v₀) N).hom
          (NativeQuarterGraphDescent.graphSupportClass P v₀ N a)) = _ at he
  rw [support_class_half_pullback m P v₀ b hρ hρr hr hη hr8 hη8] at he
  exact he.symm

end
end Finsler.NativeQuarterGraphCompatibility
