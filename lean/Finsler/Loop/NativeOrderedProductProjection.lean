module

public import Finsler.Loop.NativeOrderedPairClosing
public import Finsler.Loop.MeridianOrderedSweepInputs
public import Finsler.Loop.DoubleClosedSweepPost

/-! The two remaining nonzero ordered-cell inputs are the actual
relative projections of LEFT-associated products S,E,S and E,S,S.
Both maps to the graph model are explicit; no homology permutation
invariance or new singular-cross associator theorem is needed. -/
@[expose] public section
namespace Finsler.NativeOrderedProductProjection
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativePairRelativeSphereTransport Finsler.MeridianOrderedSweepInputs
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
def toGraph02 {n : ℕ} (P : Sphere n) : (S n ⊗ E P) ⊗ S n ⟶ graphSpace P :=
  TopCat.ofHom ⟨fun z => (z.1.1, (z.2, z.1.2)), by
    change Continuous (fun z : (Sphere n × equator P) × Sphere n => (z.1.1, (z.2, z.1.2)))
    fun_prop⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
def toGraph12 {n : ℕ} (P : Sphere n) : (E P ⊗ S n) ⊗ S n ⟶ graphSpace P :=
  TopCat.ofHom ⟨fun z => (z.1.2, (z.2, z.1.1)), by
    change Continuous (fun z : (equator P × Sphere n) × Sphere n => (z.1.2, (z.2, z.1.1)))
    fun_prop⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem model02 {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleClosedSweepProjection.squareEvaluation
      (TripleCrossClosedSweep.first (H P v₀) (E P) (E P))
      (TripleCrossClosedSweep.third (S n) (E P) (H P v₀)) ≫ toGraph02 P =
      NativeOrderedPairClosing.closedMap P v₀ 1 true := by
  apply TopCat.ext
  intro z
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem model12 {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleClosedSweepProjection.squareEvaluation
      (TripleCrossClosedSweep.third (E P) (E P) (H P v₀))
      (TripleCrossClosedSweep.second (E P) (H P v₀) (S n)) ≫ toGraph12 P =
      NativeOrderedPairClosing.closedMap P v₀ 2 false := by
  apply TopCat.ext
  intro z
  rfl

theorem faces02 {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (DoubleClosedSweepProjection.squareEvaluation
      (TripleCrossClosedSweep.first (H P v₀) (E P) (E P))
      (TripleCrossClosedSweep.third (S n) (E P) (H P v₀)) ≫ toGraph02 P)
      (DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P)) (graphBoundary P v₀) := by
  rw [model02]
  exact NativeOrderedPairClosing.closed_faces P v₀ 1 true

theorem faces12 {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (DoubleClosedSweepProjection.squareEvaluation
      (TripleCrossClosedSweep.third (E P) (E P) (H P v₀))
      (TripleCrossClosedSweep.second (E P) (H P v₀) (S n)) ≫ toGraph12 P)
      (DoubleRelativeTimeCylinder.squareBoundary (NativeGlobalTimeSquare.source P)) (graphBoundary P v₀) := by
  rw [model12]
  exact NativeOrderedPairClosing.closed_faces P v₀ 2 false

private theorem subsetMap_congr {X Y : TopCat.{0}} (A : Set X) (B : Set Y) (f g : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (h : f = g) :
    TopPair.ofSubsetMap (B := A) (B' := B) f hf = TopPair.ofSubsetMap (B := A) (B' := B) g hg := by
  subst g
  rfl

theorem pair02 {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleClosedSweepPost.pairMap (TripleCrossClosedSweep.first (H P v₀) (E P) (E P))
      (TripleCrossClosedSweep.third (S n) (E P) (H P v₀)) (toGraph02 P) (graphBoundary P v₀) (faces02 P v₀) =
      NativeOrderedPairClosing.closedPair P v₀ 1 true :=
  (DoubleClosedSweepPost.pairMap_eq _ _ _ _ _).trans (subsetMap_congr _ _ _ _ _ _ (model02 P v₀))

theorem pair12 {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleClosedSweepPost.pairMap (TripleCrossClosedSweep.third (E P) (E P) (H P v₀))
      (TripleCrossClosedSweep.second (E P) (H P v₀) (S n)) (toGraph12 P) (graphBoundary P v₀) (faces12 P v₀) =
      NativeOrderedPairClosing.closedPair P v₀ 2 false :=
  (DoubleClosedSweepPost.pairMap_eq _ _ _ _ _).trans (subsetMap_congr _ _ _ _ _ _ (model12 P v₀))

theorem closed02_projection (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeOrderedPairClosing.closedInput m hm P v₀ 1 true =
    ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom
      ((homologyPushZMod2 (toGraph02 P) (3 * m + 2)).hom (class02 m hm P)) := by
  have he := ConcreteCategory.congr_hom
    (DoubleClosedSweepPost.homology_projection (TripleCrossClosedSweep.first (H P v₀) (E P) (E P))
      (TripleCrossClosedSweep.third (S (m + 1)) (E P) (H P v₀)) (toGraph02 P)
      (graphBoundary P v₀) (faces02 P v₀) (3 * m)) (BasedMeridianProducts.tripleSource m hm P)
  rw [pair02] at he
  change NativeOrderedPairClosing.closedInput m hm P v₀ 1 true =
    ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom
      ((homologyPushZMod2 (toGraph02 P) (3 * m + 2)).hom (input02Forward m hm P v₀)) at he
  rw [forward02_value] at he
  exact he

theorem closed12_projection (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeOrderedPairClosing.closedInput m hm P v₀ 2 false =
    ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom
      ((homologyPushZMod2 (toGraph12 P) (3 * m + 2)).hom (class12 m hm P)) := by
  have he := ConcreteCategory.congr_hom
    (DoubleClosedSweepPost.homology_projection (TripleCrossClosedSweep.third (E P) (E P) (H P v₀))
      (TripleCrossClosedSweep.second (E P) (H P v₀) (S (m + 1))) (toGraph12 P)
      (graphBoundary P v₀) (faces12 P v₀) (3 * m)) (BasedMeridianProducts.tripleSource m hm P)
  rw [pair12] at he
  change NativeOrderedPairClosing.closedInput m hm P v₀ 2 false =
    ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom
      ((homologyPushZMod2 (toGraph12 P) (3 * m + 2)).hom (input12Wrapped m hm P v₀)) at he
  rw [wrapped12_value] at he
  exact he

theorem graph02_projection (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeOrderedPairClosing.graphInput m hm P v₀ 1 true =
    ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom
      ((homologyPushZMod2 (toGraph02 P) (3 * m + 2)).hom (class02 m hm P)) :=
  (NativeOrderedPairClosing.graphInput_closed m hm P v₀ 1 true).trans (closed02_projection m hm P v₀)

theorem graph12_projection (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeOrderedPairClosing.graphInput m hm P v₀ 2 false =
    ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom
      ((homologyPushZMod2 (toGraph12 P) (3 * m + 2)).hom (class12 m hm P)) :=
  (NativeOrderedPairClosing.graphInput_closed m hm P v₀ 2 false).trans (closed12_projection m hm P v₀)

end
end Finsler.NativeOrderedProductProjection
