module

public import Finsler.Loop.MeridianRelativeFundamental
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-! Close BOTH actual meridian-time coordinates simultaneously by a
genuine homotopy of the REAL sphere-product pairs. The clock grows
from t/2 to t. Every end face stays on the actual fixed return curve.
Thus the actual double-prism input can use the OLD full closed loops
without separately expanding two nested triangle corrections.
External-product compatibility and its fundamental value remain open. -/
@[expose] public section
namespace Finsler.NativeDoubleSweepClosing
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 800000

def clock (s t : _root_.unitInterval) : _root_.unitInterval :=
  ⟨(1 + (s : ℝ)) * (t : ℝ) / 2, by
    constructor <;> nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]⟩

theorem continuous_clock : Continuous (fun z : _root_.unitInterval × _root_.unitInterval => clock z.1 z.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.add continuous_fst.subtype_val).mul continuous_snd.subtype_val).div_const 2

theorem clock_one (t : _root_.unitInterval) : clock 1 t = t := by
  apply Subtype.ext
  change (1 + (1 : ℝ)) * (t : ℝ) / 2 = (t : ℝ)
  ring

theorem clock_at_zero (s : _root_.unitInterval) : clock s 0 = 0 := by
  apply Subtype.ext
  change (1 + (s : ℝ)) * (0 : ℝ) / 2 = 0
  ring

theorem loop_clock_zero {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : _root_.unitInterval) :
    loop P v₀ v (clock 0 t) = meridian P v t := by
  rw [← Path.extend_apply _ (clock 0 t).property]
  have ht : (clock 0 t : ℝ) = (t : ℝ) / 2 := by
    change (1 + (0 : ℝ)) * (t : ℝ) / 2 = _
    ring
  rw [ht]
  exact NativeMeridianMatchingLoci.loop_meridian P v₀ v t

theorem clock_end_carried {n : ℕ} (P : Sphere n) (v₀ v : equator P) (s : _root_.unitInterval) :
    loop P v₀ v (clock s 1) ∈ fixedCurve P v₀ := by
  have hh : (1 / 2 : ℝ) ≤ (clock s 1 : ℝ) := by
    change 1 / 2 ≤ (1 + (s : ℝ)) * 1 / 2
    linarith [s.property.1]
  have ha : 0 ≤ 2 * (clock s 1 : ℝ) - 1 := by linarith
  have hb : 2 * (clock s 1 : ℝ) - 1 ≤ 1 := by linarith [(clock s 1).property.2]
  refine ⟨unitInterval.symm ⟨2 * (clock s 1 : ℝ) - 1, ha, hb⟩, ?_⟩
  rw [← Path.extend_apply _ (clock s 1).property, loop, Path.extend_trans_of_half_le _ _ hh]
  exact (Path.extend_apply (meridian P v₀).symm ⟨ha, hb⟩).symm

abbrev source {n : ℕ} (P : Sphere n) := NativePairDoublePrismSource.source P
abbrev square {n : ℕ} (P : Sphere n) :=
  DoubleRelativeTimeCylinder.cylinder (DoubleRelativeTimeCylinder.cylinder (source P))

def closedTimeEvaluation {n : ℕ} (P : Sphere n) (v₀ : equator P) : square P ⟶ graphSpace P :=
  TopCat.ofHom ⟨fun z => (loop P v₀ z.2.2.1.1 z.1, (loop P v₀ z.2.2.1.2 z.2.1, z.2.2.2)), by
    have hpl : Continuous (fun z : square P => (z.1, z.2.2.1.1)) :=
      continuous_fst.prodMk continuous_snd.snd.fst.fst
    have hpr : Continuous (fun z : square P => (z.2.1, z.2.2.1.2)) :=
      continuous_snd.fst.prodMk continuous_snd.snd.fst.snd
    have hl := (MeridianRelativeSweep.fullHomotopy P v₀).continuous.comp hpl
    have hr := (MeridianRelativeSweep.fullHomotopy P v₀).continuous.comp hpr
    exact (hl.prodMk (hr.prodMk continuous_snd.snd.snd)).congr (fun _ => rfl)⟩

theorem closed_faces {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (closedTimeEvaluation P v₀) (DoubleRelativeTimeCylinder.squareBoundary (source P))
      (graphBoundary P v₀) := by
  intro z hz
  change loop P v₀ z.2.2.1.1 z.1 ∈ fixedCurve P v₀ ∨ loop P v₀ z.2.2.1.2 z.2.1 ∈ fixedCurve P v₀
  rcases hz with (h | h) | (h | h)
  · exact Or.inl ⟨0, by simp only [h, Path.source]⟩
  · exact Or.inl ⟨0, by simp only [h, Path.target, Path.source]⟩
  · exact Or.inr ⟨0, by simp only [h, Path.source]⟩
  · exact Or.inr ⟨0, by simp only [h, Path.target, Path.source]⟩

def closedPairMap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    DoubleRelativeTimeCylinder.squarePair (source P) ⟶ graphPair P v₀ :=
  TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary (source P))
    (B' := graphBoundary P v₀) (closedTimeEvaluation P v₀) (closed_faces P v₀)

def ambientHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (directTimeEvaluation P) (closedTimeEvaluation P v₀) where
  toFun z := (loop P v₀ z.2.2.2.1.1 (clock z.1 z.2.1),
    (loop P v₀ z.2.2.2.1.2 (clock z.1 z.2.2.1), z.2.2.2.2))
  continuous_toFun := by
    have htl : Continuous (fun z : _root_.unitInterval × square P => (z.1, z.2.1)) :=
      continuous_fst.prodMk continuous_snd.fst
    have htr : Continuous (fun z : _root_.unitInterval × square P => (z.1, z.2.2.1)) :=
      continuous_fst.prodMk continuous_snd.snd.fst
    have hlc := continuous_clock.comp htl
    have hrc := continuous_clock.comp htr
    have hpl : Continuous (fun z : _root_.unitInterval × square P =>
        (clock z.1 z.2.1, z.2.2.2.1.1)) := hlc.prodMk continuous_snd.snd.snd.fst.fst
    have hpr : Continuous (fun z : _root_.unitInterval × square P =>
        (clock z.1 z.2.2.1, z.2.2.2.1.2)) := hrc.prodMk continuous_snd.snd.snd.fst.snd
    have hl := (MeridianRelativeSweep.fullHomotopy P v₀).continuous.comp hpl
    have hr := (MeridianRelativeSweep.fullHomotopy P v₀).continuous.comp hpr
    exact (hl.prodMk (hr.prodMk continuous_snd.snd.snd.snd)).congr (fun _ => rfl)
  map_zero_left z := by
    change (loop P v₀ z.2.2.1.1 (clock 0 z.1), (loop P v₀ z.2.2.1.2 (clock 0 z.2.1), z.2.2.2)) = _
    rw [loop_clock_zero, loop_clock_zero]
    rfl
  map_one_left z := by
    change (loop P v₀ z.2.2.1.1 (clock 1 z.1), (loop P v₀ z.2.2.1.2 (clock 1 z.2.1), z.2.2.2)) = _
    rw [clock_one, clock_one]
    rfl

theorem homotopy_faces {n : ℕ} (P : Sphere n) (v₀ : equator P) (s : _root_.unitInterval)
    (z : square P) (hz : z ∈ DoubleRelativeTimeCylinder.squareBoundary (source P)) :
    ambientHomotopy P v₀ (s, z) ∈ graphBoundary P v₀ := by
  change loop P v₀ z.2.2.1.1 (clock s z.1) ∈ fixedCurve P v₀ ∨
    loop P v₀ z.2.2.1.2 (clock s z.2.1) ∈ fixedCurve P v₀
  rcases hz with (h | h) | (h | h)
  · left
    rw [h, clock_at_zero]
    exact ⟨0, (meridian P v₀).source.trans (loop P v₀ _).source.symm⟩
  · left
    rw [h]
    exact clock_end_carried P v₀ _ s
  · right
    rw [h, clock_at_zero]
    exact ⟨0, (meridian P v₀).source.trans (loop P v₀ _).source.symm⟩
  · right
    rw [h]
    exact clock_end_carried P v₀ _ s

def pairHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Homotopy (directPairMap P v₀) (closedPairMap P v₀) :=
  TopPair.ofSubsetHomotopy (ambientHomotopy P v₀) (homotopy_faces P v₀)

theorem homology_equal {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    TopPair.singularHomologyMap (directPairMap P v₀) coeff q =
      TopPair.singularHomologyMap (closedPairMap P v₀) coeff q := by
  exact (pairHomotopy P v₀).congr_singularHomologyMap coeff q

def closedInputClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (TopPair.singularHomologyMap (closedPairMap P v₀) coeff (3 * m + 2)).hom
    ((DoubleRelativeTimeCylinder.homology (source P) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P))

theorem graphInput_closed (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    graphInputClass m hm P v₀ = closedInputClass m hm P v₀ := by
  exact ConcreteCategory.congr_hom (homology_equal P v₀ (3 * m + 2)) _

theorem nativeInput_closed (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (TopPair.singularHomologyMap (nativeToGraph P v₀) coeff (3 * m + 2)).hom
      (NativePairDoublePrismSource.inputClass m hm P v₀) = closedInputClass m hm P v₀ :=
  (nativeInput_image m hm P v₀).trans (graphInput_closed m hm P v₀)

theorem pairing_closed (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (a : RelativeCup.cohomology (graphPair P v₀) (3 * m + 2)) :
    RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (nativeToGraph P v₀) (3 * m + 2)).hom a) (NativePairDoublePrismSource.inputClass m hm P v₀) =
      RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a (closedInputClass m hm P v₀) :=
  (pairing_transport m hm P v₀ a).trans
    (congrArg (RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a) (graphInput_closed m hm P v₀))

end
end Finsler.NativeDoubleSweepClosing
