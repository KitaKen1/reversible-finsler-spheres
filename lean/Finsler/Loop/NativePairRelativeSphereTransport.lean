module

public import Finsler.Loop.NativePairDoublePrismSource

/-! Transport the ACTUAL native double-prism relative input to the
actual sphere-product model, RELATIVE to both fixed-meridian curves.
Every time/fixed-direction face is retained and the true pair diagram
commutes. This is not an identification with an absolute sphere cross
fundamental class or a numeric normalized Thom-cap evaluation. -/
@[expose] public section
namespace Finsler.NativePairRelativeSphereTransport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def fixedCurve {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (BorelEvaluation.sphere n) :=
  Set.range (meridian P v₀)

abbrev graphSpace {n : ℕ} (P : Sphere n) : TopCat.{0} :=
  TopCat.of (BorelEvaluation.sphere n × (BorelEvaluation.sphere n × equator P))

def graphBoundary {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (graphSpace P) :=
  {z | z.1 ∈ fixedCurve P v₀ ∨ z.2.1 ∈ fixedCurve P v₀}

abbrev graphPair {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopPair.{0} :=
  TopPair.ofSubset (X := graphSpace P) (graphBoundary P v₀)

theorem native_boundary_maps {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (sphereCoordinates P) (NativePairBoundaryRelativeCut.bad P v₀) (graphBoundary P v₀) := by
  intro z hz
  change meridian P z.1.2 z.1.1 ∈ fixedCurve P v₀ ∨ meridian P z.2.1.2 z.2.1.1 ∈ fixedCurve P v₀
  rcases hz with h | h | h | h | h | h
  · exact Or.inl ⟨0, by simp only [h, Path.source]⟩
  · exact Or.inl ⟨1, by simp only [h, Path.target]⟩
  · exact Or.inr ⟨0, by simp only [h, Path.source]⟩
  · exact Or.inr ⟨1, by simp only [h, Path.target]⟩
  · exact Or.inl ⟨z.1.1, by rw [h]⟩
  · exact Or.inr ⟨z.2.1.1, by rw [h]⟩

def nativeToGraph {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativePairBoundaryRelativeCut.pair P v₀ ⟶ graphPair P v₀ :=
  TopPair.ofSubsetMap (B := NativePairBoundaryRelativeCut.bad P v₀) (B' := graphBoundary P v₀)
    (sphereCoordinates P) (native_boundary_maps P v₀)

def directTimeEvaluation {n : ℕ} (P : Sphere n) :
    DoubleRelativeTimeCylinder.cylinder (DoubleRelativeTimeCylinder.cylinder (NativePairDoublePrismSource.source P)) ⟶
      graphSpace P :=
  TopCat.ofHom ⟨fun z => (meridianEvaluation P (z.1, z.2.2.1.1),
    (meridianEvaluation P (z.2.1, z.2.2.1.2), z.2.2.2)),
    ((meridianEvaluation P).hom.continuous.comp (continuous_fst.prodMk continuous_snd.snd.fst.fst)).prodMk
      (((meridianEvaluation P).hom.continuous.comp (continuous_snd.fst.prodMk continuous_snd.snd.fst.snd)).prodMk
        continuous_snd.snd.snd)⟩

theorem ambient_factor {n : ℕ} (P : Sphere n) :
    NativePairDoublePrismSource.reorder P ≫ sphereCoordinates P = directTimeEvaluation P := by
  apply TopCat.ext
  intro z
  rfl

theorem time_faces_map {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (directTimeEvaluation P)
      (DoubleRelativeTimeCylinder.squareBoundary (NativePairDoublePrismSource.source P)) (graphBoundary P v₀) := by
  intro z hz
  have he := ConcreteCategory.congr_hom (ambient_factor P) z
  exact he ▸ native_boundary_maps P v₀ (NativePairDoublePrismSource.faces_map P v₀ hz)

def directPairMap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleRelativeTimeCylinder.squarePair (NativePairDoublePrismSource.source P) ⟶ graphPair P v₀ :=
  TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary (NativePairDoublePrismSource.source P))
    (B' := graphBoundary P v₀) (directTimeEvaluation P) (time_faces_map P v₀)

private theorem subsetMap_congr {X Y : TopCat.{0}} (A : Set X) (B : Set Y) (f g : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (h : f = g) :
    TopPair.ofSubsetMap (B := A) (B' := B) f hf = TopPair.ofSubsetMap (B := A) (B' := B) g hg := by
  subst g
  rfl

theorem pair_composition {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativePairDoublePrismSource.pairMap P v₀ ≫ nativeToGraph P v₀ = directPairMap P v₀ := by
  have he := TopPair.ofSubsetMap_comp (NativePairDoublePrismSource.reorder P) (sphereCoordinates P)
    (NativePairDoublePrismSource.faces_map P v₀) (native_boundary_maps P v₀)
    (fun z hz => native_boundary_maps P v₀ (NativePairDoublePrismSource.faces_map P v₀ hz))
  exact he.symm.trans (subsetMap_congr _ _ _ _ _ _ (ambient_factor P))

def graphInputClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (TopPair.singularHomologyMap (directPairMap P v₀) coeff (3 * m + 2)).hom
    ((DoubleRelativeTimeCylinder.homology (NativePairDoublePrismSource.source P) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

theorem nativeInput_image (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (TopPair.singularHomologyMap (nativeToGraph P v₀) coeff (3 * m + 2)).hom
      (NativePairDoublePrismSource.inputClass m hm P v₀) = graphInputClass m hm P v₀ := by
  have hc := TopPair.singularHomologyMap_comp (R := coeff)
    (f := NativePairDoublePrismSource.pairMap P v₀) (nativeToGraph P v₀) (3 * m + 2)
  rw [pair_composition] at hc
  have he := ConcreteCategory.congr_hom hc
    ((DoubleRelativeTimeCylinder.homology (NativePairDoublePrismSource.source P) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))
  exact he.symm

theorem pairing_transport (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (a : RelativeCup.cohomology (graphPair P v₀) (3 * m + 2)) :
    RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (nativeToGraph P v₀) (3 * m + 2)).hom a) (NativePairDoublePrismSource.inputClass m hm P v₀) =
      RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a (graphInputClass m hm P v₀) := by
  have he := congrArg (fun f => f (NativePairDoublePrismSource.inputClass m hm P v₀))
    (RelativeKronecker.naturality (nativeToGraph P v₀) (3 * m + 2) a)
  exact he.trans (congrArg (RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a)
    (nativeInput_image m hm P v₀))

end
end Finsler.NativePairRelativeSphereTransport
