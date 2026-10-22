module

public import Finsler.Loop.NativeNorthSupportPatch

/-! Descend the SAME original native supported cut class to the REAL
sphere-graph relative pair. Actual north-chart pair isomorphism and
actual excision invert its support pullback. The exact boundary/support
square proves the ORIGINAL class pullback, without postulating a
graph class or replacing any original cochain/radius/tested data. -/
@[expose] public section
namespace Finsler.NativeCutGraphDescent
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates
open Finsler.NativePairRelativeSphereTransport Finsler.NativeNorthSupportPatch
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

abbrev graphSupportPair {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopPair.{0} :=
  TopPair.ofSubset (X := graphSpace P) (graphGood P v₀)ᶜ

def supportMap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativePairGoodCarrier.supportPair P v₀ ⟶ graphSupportPair P v₀ :=
  TopPair.ofSubsetMap (B := (NativePairGoodCarrier.good P v₀)ᶜ) (B' := (graphGood P v₀)ᶜ)
    (sphereCoordinates P) (maps_support P v₀)

theorem support_homology_isIso {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    IsIso (TopPair.singularHomologyMap (supportMap P v₀) coeff q) := by
  have := patchPair_isIso P v₀
  exact RelativeSupportPatchExcision.homology_isIso (sphereCoordinates P) (maps_patch P) (maps_support P v₀)
    (native_cover P v₀) (graph_cover P v₀) q

def supportEquiv {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    RelativeCup.cohomology (graphSupportPair P v₀) q ≃ₗ[ZMod 2]
      RelativeCup.cohomology (NativePairGoodCarrier.supportPair P v₀) q := by
  have := support_homology_isIso P v₀ q
  exact RelativeHomologyIsoCohomology.equiv (supportMap P v₀) q

theorem supportEquiv_apply {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : RelativeCup.cohomology (graphSupportPair P v₀) q) :
    supportEquiv P v₀ q a = (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (supportMap P v₀) q).hom a := by
  have := support_homology_isIso P v₀ q
  exact RelativeHomologyIsoCohomology.equiv_apply (supportMap P v₀) q a

theorem graphBoundary_outside {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    graphBoundary P v₀ ⊆ (graphGood P v₀)ᶜ := by
  intro z hz hg
  rcases hz with ⟨t, ht⟩ | ⟨t, ht⟩
  · have he := NorthMeridianEvaluationPoint.excluded_distance P v₀
      ⟨meridian P v₀ t, NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ t⟩
    change (3 / 5 : ℝ) ≤ ‖(meridian P v₀ t : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ at he
    rw [ht] at he
    linarith [hg.1]
  · have he := NorthMeridianEvaluationPoint.excluded_distance P v₀
      ⟨meridian P v₀ t, NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ t⟩
    change (3 / 5 : ℝ) ≤ ‖(meridian P v₀ t : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ at he
    rw [ht] at he
    linarith [hg.2]

def graphBoundaryToSupport {n : ℕ} (P : Sphere n) (v₀ : equator P) : graphPair P v₀ ⟶ graphSupportPair P v₀ :=
  TopPair.ofSubsetMap (B := graphBoundary P v₀) (B' := (graphGood P v₀)ᶜ)
    (𝟙 (graphSpace P)) (graphBoundary_outside P v₀)

private theorem subsetMap_congr {X Y : TopCat.{0}} (A : Set X) (B : Set Y) (f g : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (h : f = g) :
    TopPair.ofSubsetMap (B := A) (B' := B) f hf = TopPair.ofSubsetMap (B := A) (B' := B) g hg := by
  subst g
  rfl

theorem boundary_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativePairGoodCarrier.boundaryToSupport P v₀ ≫ supportMap P v₀ =
      nativeToGraph P v₀ ≫ graphBoundaryToSupport P v₀ := by
  let h := fun z (hz : z ∈ NativePairBoundaryRelativeCut.bad P v₀) =>
    maps_support P v₀ (NativePairGoodCarrier.bad_outside P v₀ z hz)
  have hl : TopPair.ofSubsetMap (B := NativePairBoundaryRelativeCut.bad P v₀) (B' := (graphGood P v₀)ᶜ)
      (𝟙 (parameters P) ≫ sphereCoordinates P) h = NativePairGoodCarrier.boundaryToSupport P v₀ ≫ supportMap P v₀ :=
    TopPair.ofSubsetMap_comp (𝟙 (parameters P)) (sphereCoordinates P)
      (fun z hz => NativePairGoodCarrier.bad_outside P v₀ z hz) (maps_support P v₀) h
  have hr : TopPair.ofSubsetMap (B := NativePairBoundaryRelativeCut.bad P v₀) (B' := (graphGood P v₀)ᶜ)
      (sphereCoordinates P ≫ 𝟙 (graphSpace P)) h = nativeToGraph P v₀ ≫ graphBoundaryToSupport P v₀ :=
    TopPair.ofSubsetMap_comp (sphereCoordinates P) (𝟙 (graphSpace P))
      (native_boundary_maps P v₀) (graphBoundary_outside P v₀) h
  have hlc := subsetMap_congr (NativePairBoundaryRelativeCut.bad P v₀) (graphGood P v₀)ᶜ
    (𝟙 (parameters P) ≫ sphereCoordinates P) (sphereCoordinates P) h h (Category.id_comp _)
  have hrc := subsetMap_congr (NativePairBoundaryRelativeCut.bad P v₀) (graphGood P v₀)ᶜ
    (sphereCoordinates P ≫ 𝟙 (graphSpace P)) (sphereCoordinates P) h h (Category.comp_id _)
  exact (hl.symm.trans hlc).trans (hr.symm.trans hrc).symm

def graphSupportClass {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : RelativeCup.cohomology (NativePairGoodCarrier.supportPair P v₀) q) :
    RelativeCup.cohomology (graphSupportPair P v₀) q := (supportEquiv P v₀ q).symm a

theorem support_pullback {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : RelativeCup.cohomology (NativePairGoodCarrier.supportPair P v₀) q) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (supportMap P v₀) q).hom
      (graphSupportClass P v₀ q a) = a :=
  (supportEquiv_apply P v₀ q _).symm.trans ((supportEquiv P v₀ q).apply_symm_apply a)

def graphClass {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : RelativeCup.cohomology (NativePairGoodCarrier.supportPair P v₀) q) :
    RelativeCup.cohomology (graphPair P v₀) q :=
  (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (graphBoundaryToSupport P v₀) q).hom
    (graphSupportClass P v₀ q a)

theorem graphClass_pullback {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : RelativeCup.cohomology (NativePairGoodCarrier.supportPair P v₀) q) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (nativeToGraph P v₀) q).hom
      (graphClass P v₀ q a) =
      (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (NativePairGoodCarrier.boundaryToSupport P v₀) q).hom a := by
  have he := congrArg (fun f => (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom
    (graphSupportClass P v₀ q a)) (boundary_square P v₀)
  rw [TopPair.singularCohomologyMap_comp, TopPair.singularCohomologyMap_comp] at he
  change (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (NativePairGoodCarrier.boundaryToSupport P v₀) q).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (supportMap P v₀) q).hom
        (graphSupportClass P v₀ q a)) = _ at he
  exact he.symm.trans (congrArg (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (NativePairGoodCarrier.boundaryToSupport P v₀) q).hom (support_pullback P v₀ q a))

def originalGraphClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :=
  graphClass P v₀ ((m + 1) + (m + (m + 1)))
    (NativePairGoodCarrier.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr4 hη4)

theorem originalGraphClass_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (nativeToGraph P v₀)
      ((m + 1) + (m + (m + 1)))).hom (originalGraphClass m P v₀ b hρ hρr hr hη hr4 hη4) =
      NativePairBoundaryRelativeCut.originalPrimitiveClass m P v₀ b hρ hρr hr hη hr4 hη4 :=
  (graphClass_pullback P v₀ _ _).trans
    (NativePairGoodCarrier.originalPrimitiveSupportClass_pullback m P v₀ b hρ hρr hr hη hr4 hη4)

end
end Finsler.NativeCutGraphDescent
