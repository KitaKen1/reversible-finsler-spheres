module

public import Finsler.Loop.NativeOrderedPairCoordinates
public import Finsler.Loop.NativeDoubleSweepClosing

/-! Close each ACTUAL ordered meridian pair while leaving its original
source class unchanged. Source directions and both times are merely
read by explicit coordinate maps. The real pair homotopy retains all
boundary faces. No permutation or time-exchange input invariance is
assumed by the native-to-graph comparison. -/
@[expose] public section
namespace Finsler.NativeOrderedPairClosing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativePairRelativeSphereTransport
open Finsler.NativeOrderedPairCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1400000

def reorderedSquare {n : ℕ} (P : Sphere n) (b : Fin 3) (forward : Bool) :
    NativeGlobalTimeSquare.squareDomain P ⟶ NativeGlobalTimeSquare.squareDomain P :=
  TopCat.ofHom ⟨fun z => (if forward then z.2.1 else z.1,
    (if forward then z.1 else z.2.1, sourceOrder b z.2.2)), by
    cases forward <;> fin_cases b <;> dsimp [sourceOrder] <;> fun_prop⟩

theorem reordered_faces {n : ℕ} (P : Sphere n) (b : Fin 3) (forward : Bool) :
    Set.MapsTo (reorderedSquare P b forward)
      (DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P))
      (DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P)) := by
  intro z hz
  cases forward
  · exact hz
  · rcases hz with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem coordinates_reorder {n : ℕ} (P : Sphere n) (b : Fin 3) (forward : Bool) :
    reorderedSquare P b forward ≫ NativePairDoublePrismSource.reorder P = coordinates P b forward := by
  apply TopCat.ext
  intro z
  rfl

def directMap {n : ℕ} (P : Sphere n) (b : Fin 3) (forward : Bool) :
    NativeGlobalTimeSquare.squareDomain P ⟶ graphSpace P :=
  reorderedSquare P b forward ≫ NativePairRelativeSphereTransport.directTimeEvaluation P

def closedMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    NativeGlobalTimeSquare.squareDomain P ⟶ graphSpace P :=
  reorderedSquare P b forward ≫ NativeDoubleSweepClosing.closedTimeEvaluation P v₀

theorem direct_faces {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    Set.MapsTo (directMap P b forward)
      (DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P)) (graphBoundary P v₀) :=
  fun _z hz => NativePairRelativeSphereTransport.time_faces_map P v₀ (reordered_faces P b forward hz)

theorem closed_faces {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    Set.MapsTo (closedMap P v₀ b forward)
      (DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P)) (graphBoundary P v₀) :=
  fun _z hz => NativeDoubleSweepClosing.closed_faces P v₀ (reordered_faces P b forward hz)

def directPair {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    DoubleRelativeTimeCylinder.squarePair (NativeGlobalTimeSquare.source P) ⟶ graphPair P v₀ :=
  TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P))
    (B' := graphBoundary P v₀) (directMap P b forward) (direct_faces P v₀ b forward)

def closedPair {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    DoubleRelativeTimeCylinder.squarePair (NativeGlobalTimeSquare.source P) ⟶ graphPair P v₀ :=
  TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P))
    (B' := graphBoundary P v₀) (closedMap P v₀ b forward) (closed_faces P v₀ b forward)

private theorem subsetMap_congr {X Y : TopCat.{0}} (A : Set X) (B : Set Y) (f g : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (h : f = g) :
    TopPair.ofSubsetMap (B := A) (B' := B) f hf = TopPair.ofSubsetMap (B := A) (B' := B) g hg := by
  subst g
  rfl

theorem pair_composition {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    NativeOrderedPairCoordinates.pairMap P v₀ b forward ≫ nativeToGraph P v₀ = directPair P v₀ b forward := by
  have he := TopPair.ofSubsetMap_comp (coordinates P b forward) (NativeMeridianPairCoordinates.sphereCoordinates P)
    (NativeOrderedPairCoordinates.faces P v₀ b forward) (native_boundary_maps P v₀)
    (fun z hz => native_boundary_maps P v₀ (NativeOrderedPairCoordinates.faces P v₀ b forward hz))
  have hg : coordinates P b forward ≫ NativeMeridianPairCoordinates.sphereCoordinates P = directMap P b forward := by
    apply TopCat.ext
    intro z
    rfl
  exact he.symm.trans (subsetMap_congr _ _ _ _ _ _ hg)

def ambientHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    TopCat.Homotopy (directMap P b forward) (closedMap P v₀ b forward) :=
  (NativeDoubleSweepClosing.ambientHomotopy P v₀).comp (TopCat.Homotopy.refl (reorderedSquare P b forward))

theorem homotopy_faces {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool)
    (s : _root_.unitInterval) (z : NativeGlobalTimeSquare.squareDomain P)
    (hz : z ∈ DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P)) :
    ambientHomotopy P v₀ b forward (s, z) ∈ graphBoundary P v₀ :=
  NativeDoubleSweepClosing.homotopy_faces P v₀ s (reorderedSquare P b forward z) (reordered_faces P b forward hz)

def pairHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    TopPair.Homotopy (directPair P v₀ b forward) (closedPair P v₀ b forward) :=
  TopPair.ofSubsetHomotopy (ambientHomotopy P v₀ b forward) (homotopy_faces P v₀ b forward)

theorem homology_equal {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (forward : Bool) (q : ℕ) :
    TopPair.singularHomologyMap (directPair P v₀ b forward) coeff q =
      TopPair.singularHomologyMap (closedPair P v₀ b forward) coeff q :=
  (pairHomotopy P v₀ b forward).congr_singularHomologyMap coeff q

def nativeInput (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (forward : Bool) :=
  (TopPair.singularHomologyMap (NativeOrderedPairCoordinates.pairMap P v₀ b forward) coeff (3 * m + 2)).hom
    ((DoubleRelativeTimeCylinder.homology (NativeGlobalTimeSquare.source P) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

def graphInput (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (forward : Bool) :=
  (TopPair.singularHomologyMap (directPair P v₀ b forward) coeff (3 * m + 2)).hom
    ((DoubleRelativeTimeCylinder.homology (NativeGlobalTimeSquare.source P) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

def closedInput (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (forward : Bool) :=
  (TopPair.singularHomologyMap (closedPair P v₀ b forward) coeff (3 * m + 2)).hom
    ((DoubleRelativeTimeCylinder.homology (NativeGlobalTimeSquare.source P) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

theorem nativeInput_image (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    (TopPair.singularHomologyMap (nativeToGraph P v₀) coeff (3 * m + 2)).hom
      (nativeInput m hm P v₀ b forward) = graphInput m hm P v₀ b forward := by
  have hc := TopPair.singularHomologyMap_comp (R := coeff)
    (f := NativeOrderedPairCoordinates.pairMap P v₀ b forward) (nativeToGraph P v₀) (3 * m + 2)
  rw [pair_composition] at hc
  exact (ConcreteCategory.congr_hom hc
    ((DoubleRelativeTimeCylinder.homology (NativeGlobalTimeSquare.source P) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))).symm

theorem graphInput_closed (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (forward : Bool) :
    graphInput m hm P v₀ b forward = closedInput m hm P v₀ b forward :=
  ConcreteCategory.congr_hom (homology_equal P v₀ b forward (3 * m + 2)) _

end
end Finsler.NativeOrderedPairClosing
