module

public import Finsler.Loop.RelativeClosingPrism
public import Finsler.Loop.NativePairRelativeSphereTransport
public import Finsler.Loop.MeridianRotationClasses

/-! The ACTUAL variable-meridian interval sweep modulo the REAL
fixed-meridian curve equals the ORIGINAL closed meridian-loop sweep
followed by the true relative quotient. Hence its actual source
fundamental IMAGE is exactly the relative image of the EXISTING
sphere fundamental. No double-product compatibility is assumed. -/
@[expose] public section
namespace Finsler.MeridianRelativeSweep
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 900000

abbrev source {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (equator P)
abbrev curve {n : ℕ} (P : Sphere n) (v₀ : equator P) := NativePairRelativeSphereTransport.fixedCurve P v₀
abbrev pair {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopPair.{0} :=
  TopPair.ofSubset (X := BorelEvaluation.sphere n) (curve P v₀)

def constant {n : ℕ} (P Q : Sphere n) : source P ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom (ContinuousMap.const (equator P) Q)

def fullHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (constant P P) (constant P P) where
  toFun z := loop P v₀ z.2 z.1
  continuous_toFun := by
    have hc := (Path.continuous_uncurry_iff.mpr (loop_continuous P v₀)).comp continuous_swap
    exact hc.congr (fun _ => rfl)
  map_zero_left v := (loop P v₀ v).source
  map_one_left v := (loop P v₀ v).target

def variableHomotopy {n : ℕ} (P : Sphere n) :
    TopCat.Homotopy (constant P P) (constant P (antipode P)) where
  toFun z := meridian P z.2 z.1
  continuous_toFun := by
    have hc := (Path.continuous_uncurry_iff.mpr (meridian_continuous P)).comp continuous_swap
    exact hc.congr (fun _ => rfl)
  map_zero_left v := (meridian P v).source
  map_one_left v := (meridian P v).target

def returnHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (constant P (antipode P)) (constant P P) where
  toFun z := (meridian P v₀).symm z.1
  continuous_toFun := (meridian P v₀).symm.continuous.comp continuous_fst
  map_zero_left _ := (meridian P v₀).symm.source
  map_one_left _ := (meridian P v₀).symm.target

theorem start_range {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : source P) : constant P P v ∈ curve P v₀ :=
  ⟨0, (meridian P v₀).source⟩
theorem finish_range {n : ℕ} (P : Sphere n) (v₀ : equator P) (v : source P) : constant P (antipode P) v ∈ curve P v₀ :=
  ⟨1, (meridian P v₀).target⟩

theorem return_range {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : _root_.unitInterval × source P) :
    returnHomotopy P v₀ z ∈ curve P v₀ := ⟨unitInterval.symm z.1, rfl⟩

theorem first_map {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    UncappedTimeSplit.first (fullHomotopy P v₀).h = (variableHomotopy P).h := by
  apply TopCat.ext
  intro z
  change loop P v₀ z.1 ((IntervalTriangle.firstMap z.2).down) = meridian P z.1 z.2.down
  rw [← Path.extend_apply _ (IntervalTriangle.firstMap z.2).down.property]
  change (loop P v₀ z.1).extend ((z.2.down : ℝ) / 2) = _
  exact NativeMeridianMatchingLoci.loop_meridian P v₀ z.1 z.2.down

theorem second_map {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    UncappedTimeSplit.second (fullHomotopy P v₀).h = (returnHomotopy P v₀).h := by
  apply TopCat.ext
  intro z
  change loop P v₀ z.1 ((IntervalTriangle.secondMap z.2).down) = (meridian P v₀).symm z.2.down
  rw [← Path.extend_apply _ (IntervalTriangle.secondMap z.2).down.property]
  change (loop P v₀ z.1).extend ((1 + (z.2.down : ℝ)) / 2) = _
  rw [loop, Path.extend_trans_of_half_le _ _ (by linarith [z.2.down.property.1]),
    show 2 * ((1 + (z.2.down : ℝ)) / 2) - 1 = (z.2.down : ℝ) by ring]
  exact Path.extend_apply _ z.2.down.property

theorem full_timeMap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    (fullHomotopy P v₀).h = MeridianSweepQuarterMaps.fullMap P v₀ := by
  apply TopCat.ext
  intro z
  exact (MeridianSweepQuarterMaps.fullMap_apply P v₀ z).symm

theorem full_prism {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    ((fullHomotopy P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) =
      (push (ordinary P v₀)).f q ≫ (ContinuousLoopSweep.chainHomotopy n).hom q (q + 1) := by
  have he := UncappedTimeSplit.prism_component (fullHomotopy P v₀) q
  rw [full_timeMap] at he
  exact he.symm.trans (MeridianSweepQuarterMaps.original_prism P v₀ q).symm

theorem full_original_homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    SelfHomotopySweep.homology ((fullHomotopy P v₀).toSSet.chainComplexMap coeff) q =
      homologyPushZMod2 (ordinary P v₀) q ≫ ContinuousLoopSweep.homology n q := by
  have he := SelfHomotopySweepNaturality.homology ((fullHomotopy P v₀).toSSet.chainComplexMap coeff)
    (ContinuousLoopSweep.chainHomotopy n) (push (ordinary P v₀)) (𝟙 (chains (BorelEvaluation.sphere n)))
    (fun k => by
      rw [HomologicalComplex.id_f, Category.comp_id]
      exact (full_prism P v₀ k).symm) q
  rw [HomologicalComplex.homologyMap_id, Category.comp_id] at he
  exact he.symm

def homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  SelfHomotopySweep.homology (RelativePrismSweep.ordinary (curve P v₀) (variableHomotopy P)
    (start_range P v₀) (finish_range P v₀)) q

theorem original_projection {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    homology P v₀ q =
      (homologyPushZMod2 (ordinary P v₀) q ≫ ContinuousLoopSweep.homology n q) ≫
        HomologicalComplex.homologyMap ((pair P v₀).singularChainComplexπ coeff) (q + 1) := by
  have he := RelativeClosingPrism.closing_projection (curve P v₀) (fullHomotopy P v₀)
    (variableHomotopy P) (returnHomotopy P v₀) (start_range P v₀) (finish_range P v₀)
    (first_map P v₀) (second_map P v₀) (return_range P v₀) q
  rw [full_original_homology] at he
  exact he

def image (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (homology P v₀ m).hom (MeridianEquatorHomology.fundamental m hm P)

theorem image_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    image m hm P v₀ = ((pair P v₀).singularHomologyπ coeff (m + 1)).hom
      (SphereUnitCandidate.fundamental (m + 1) (by omega)) := by
  have he := ConcreteCategory.congr_hom (original_projection P v₀ m) (MeridianEquatorHomology.fundamental m hm P)
  change image m hm P v₀ = ((pair P v₀).singularHomologyπ coeff (m + 1)).hom
    (MeridianLoopClass.sweepClass m hm P v₀) at he
  exact he.trans (congrArg ((pair P v₀).singularHomologyπ coeff (m + 1)).hom
    (MeridianRotationClasses.sweep_fundamental m hm P v₀))

end
end Finsler.MeridianRelativeSweep
