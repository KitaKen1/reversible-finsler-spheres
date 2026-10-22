module

public import Finsler.Loop.DoubleClosedSweepProjection
public import Finsler.Loop.NativeDoubleSweepClosing

/-! The ACTUAL native graph relative input is the relative image of
TWO genuine ordinary closed meridian self-sweeps of the OLD triple
equator source. Both loops, coordinate order and the true quotient
are preserved. The external-cross/fundamental calculation remains. -/
@[expose] public section
namespace Finsler.NativeDoubleAbsoluteSweep
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 900000

abbrev source {n : ℕ} (P : Sphere n) := NativePairDoublePrismSource.source P
abbrev middle {n : ℕ} (P : Sphere n) : TopCat.{0} :=
  TopCat.of (equator P × (BorelEvaluation.sphere n × equator P))

def firstBase {n : ℕ} (P : Sphere n) : source P ⟶ middle P :=
  TopCat.ofHom ⟨fun z => (z.1.1, (P, z.2)),
    continuous_fst.fst.prodMk (continuous_const.prodMk continuous_snd)⟩

def firstHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (firstBase P) (firstBase P) where
  toFun z := (z.2.1.1, (loop P v₀ z.2.1.2 z.1, z.2.2))
  continuous_toFun := by
    have hp : Continuous (fun z : _root_.unitInterval × source P => (z.1, z.2.1.2)) :=
      continuous_fst.prodMk continuous_snd.fst.snd
    have hl := (MeridianRelativeSweep.fullHomotopy P v₀).continuous.comp hp
    exact (continuous_snd.fst.fst.prodMk (hl.prodMk continuous_snd.snd)).congr (fun _ => rfl)
  map_zero_left z := by
    change (z.1.1, (loop P v₀ z.1.2 0, z.2)) = (z.1.1, (P, z.2))
    rw [Path.source]
  map_one_left z := by
    change (z.1.1, (loop P v₀ z.1.2 1, z.2)) = (z.1.1, (P, z.2))
    rw [Path.target]

def secondBase {n : ℕ} (P : Sphere n) : middle P ⟶ graphSpace P :=
  TopCat.ofHom ⟨fun z => (P, z.2), continuous_const.prodMk continuous_snd⟩

def secondHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (secondBase P) (secondBase P) where
  toFun z := (loop P v₀ z.2.1 z.1, z.2.2)
  continuous_toFun := by
    have hp : Continuous (fun z : _root_.unitInterval × middle P => (z.1, z.2.1)) :=
      continuous_fst.prodMk continuous_snd.fst
    have hl := (MeridianRelativeSweep.fullHomotopy P v₀).continuous.comp hp
    exact (hl.prodMk continuous_snd.snd).congr (fun _ => rfl)
  map_zero_left z := by
    change (loop P v₀ z.1 0, z.2) = (P, z.2)
    rw [Path.source]
  map_one_left z := by
    change (loop P v₀ z.1 1, z.2) = (P, z.2)
    rw [Path.target]

theorem square_evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleClosedSweepProjection.squareEvaluation (firstHomotopy P v₀) (secondHomotopy P v₀) =
      NativeDoubleSweepClosing.closedTimeEvaluation P v₀ := by
  apply TopCat.ext
  intro z
  rfl

theorem faces {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (DoubleClosedSweepProjection.squareEvaluation (firstHomotopy P v₀) (secondHomotopy P v₀))
      (DoubleRelativeTimeCylinder.squareBoundary (source P)) (graphBoundary P v₀) := by
  rw [square_evaluation]
  exact NativeDoubleSweepClosing.closed_faces P v₀

private theorem subsetMap_congr {X Y : TopCat.{0}} (A : Set X) (B : Set Y) (f g : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (h : f = g) :
    TopPair.ofSubsetMap (B := A) (B' := B) f hf = TopPair.ofSubsetMap (B := A) (B' := B) g hg := by
  subst g
  rfl

theorem pairMap_eq {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleClosedSweepProjection.pairMap (firstHomotopy P v₀) (secondHomotopy P v₀)
      (graphBoundary P v₀) (faces P v₀) = NativeDoubleSweepClosing.closedPairMap P v₀ := by
  exact subsetMap_congr _ _ _ _ _ _ (square_evaluation P v₀)

def absoluteHomology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  SelfHomotopySweep.homology ((firstHomotopy P v₀).toSSet.chainComplexMap coeff) q ≫
    SelfHomotopySweep.homology ((secondHomotopy P v₀).toSSet.chainComplexMap coeff) (q + 1)

theorem relative_projection {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    DoubleRelativeTimeCylinder.homology (source P) q ≫
      TopPair.singularHomologyMap (NativeDoubleSweepClosing.closedPairMap P v₀) coeff (q + 2) =
      absoluteHomology P v₀ q ≫ HomologicalComplex.homologyMap
        ((graphPair P v₀).singularChainComplexπ coeff) (q + 2) := by
  have he := DoubleClosedSweepProjection.homology (firstHomotopy P v₀) (secondHomotopy P v₀)
    (graphBoundary P v₀) (faces P v₀) q
  change DoubleRelativeTimeCylinder.homology (source P) q ≫
    TopPair.singularHomologyMap (DoubleClosedSweepProjection.pairMap (firstHomotopy P v₀) (secondHomotopy P v₀)
      (graphBoundary P v₀) (faces P v₀)) coeff (q + 2) = _ at he
  rw [pairMap_eq] at he
  exact he

def absoluteInputClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (absoluteHomology P v₀ (3 * m)).hom (BasedMeridianProducts.tripleSource m hm P)

theorem closedInput_projection (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeDoubleSweepClosing.closedInputClass m hm P v₀ =
      ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom (absoluteInputClass m hm P v₀) := by
  exact ConcreteCategory.congr_hom (relative_projection P v₀ (3 * m)) _

theorem graphInput_projection (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    graphInputClass m hm P v₀ =
      ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom (absoluteInputClass m hm P v₀) :=
  (NativeDoubleSweepClosing.graphInput_closed m hm P v₀).trans (closedInput_projection m hm P v₀)

theorem nativeInput_projection (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (TopPair.singularHomologyMap (nativeToGraph P v₀) coeff (3 * m + 2)).hom
      (NativePairDoublePrismSource.inputClass m hm P v₀) =
      ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom (absoluteInputClass m hm P v₀) :=
  (NativeDoubleSweepClosing.nativeInput_closed m hm P v₀).trans (closedInput_projection m hm P v₀)

theorem relative_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (a : RelativeCup.cohomology (graphPair P v₀) (3 * m + 2)) :
    RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a (graphInputClass m hm P v₀) =
      (kroneckerMap (graphSpace P) (3 * m + 2)).hom
        ((relativeToPool (graphPair P v₀) (3 * m + 2)).hom a) (absoluteInputClass m hm P v₀) := by
  rw [graphInput_projection]
  exact congrArg (fun φ => φ (absoluteInputClass m hm P v₀))
    (RelativeKronecker.fromRelative_comparison (graphPair P v₀) (3 * m + 2) a)

end
end Finsler.NativeDoubleAbsoluteSweep
