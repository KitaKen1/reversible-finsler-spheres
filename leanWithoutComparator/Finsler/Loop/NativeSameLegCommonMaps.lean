module

public import Finsler.Loop.CommonMeridianThomSeamCorrection

/-! Explicit maps from both ORIGINAL chronological same-leg families
to the SAME two-time/local-direction model. The actual first and
second sphere maps commute, both real seam faces map to its diagonal,
and all original exterior radii are preserved exactly. -/
@[expose] public section
namespace Finsler.NativeSameLegCommonMaps
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelEvaluation Finsler.NativeSameLegClockGeometry Finsler.NativeMovingNonnorthGeometry
open Finsler.SameMeridianTransverseEscape Finsler.CommonMeridianThomPrimitive
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem start_continuous {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    Continuous (fun z : localSpace P v₀ k => z.val.1.1) := by
  change Continuous (fun z : {z : (ClosedInterval × NativeH1TripleMeridian.parameters P) × ULift ClosedInterval // z ∈ localSet P v₀ k} => z.val.1.1)
  fun_prop

theorem cut_continuous {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    Continuous (fun z : localSpace P v₀ k => z.val.2.down) := by
  change Continuous (fun z : {z : (ClosedInterval × NativeH1TripleMeridian.parameters P) × ULift ClosedInterval // z ∈ localSet P v₀ k} => z.val.2.down)
  fun_prop

theorem later_continuous : Continuous (fun z : ClosedInterval × ClosedInterval => later z.1 z.2) := by
  unfold later
  fun_prop

theorem earlier_continuous : Continuous (fun z : ClosedInterval × ClosedInterval => earlier z.1 z.2) := by
  unfold earlier
  fun_prop

def shortMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    localSpace P v₀ k ⟶ base P (NorthMeridianEvaluationPoint.opposite v₀) :=
  TopCat.ofHom ⟨fun z => ((z.val.1.1, later z.val.1.1 z.val.2.down), direction P v₀ k z),
    ((start_continuous P v₀ k).prodMk
      (later_continuous.comp ((start_continuous P v₀ k).prodMk (cut_continuous P v₀ k)))).prodMk
      (direction P v₀ k).hom.continuous⟩

def longMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    localSpace P v₀ k ⟶ base P (NorthMeridianEvaluationPoint.opposite v₀) :=
  TopCat.ofHom ⟨fun z => ((z.val.1.1, earlier z.val.1.1 z.val.2.down), direction P v₀ k z),
    ((start_continuous P v₀ k).prodMk
      (earlier_continuous.comp ((start_continuous P v₀ k).prodMk (cut_continuous P v₀ k)))).prodMk
      (direction P v₀ k).hom.continuous⟩

theorem short_first {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    shortMap P v₀ k ≫ firstPoint P (NorthMeridianEvaluationPoint.opposite v₀) = first P v₀ k := by
  apply TopCat.ext
  intro z
  exact (first_value P v₀ k z).symm

theorem long_first {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    longMap P v₀ k ≫ firstPoint P (NorthMeridianEvaluationPoint.opposite v₀) = first P v₀ k := by
  apply TopCat.ext
  intro z
  exact (first_value P v₀ k z).symm

theorem short_second {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    shortMap P v₀ k ≫ secondPoint P (NorthMeridianEvaluationPoint.opposite v₀) = shortEnd P v₀ k := by
  apply TopCat.ext
  intro z
  exact (NativeSameLegClockGeometry.short_endpoint P v₀ k z.val).symm

theorem long_second {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    longMap P v₀ k ≫ secondPoint P (NorthMeridianEvaluationPoint.opposite v₀) = longEnd P v₀ k := by
  apply TopCat.ext
  intro z
  exact (NativeSameLegClockGeometry.long_endpoint P v₀ k z.val).symm

theorem short_pair {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    shortMap P v₀ k ≫ OrthogonalSphereEscape.pair (firstPoint P (NorthMeridianEvaluationPoint.opposite v₀))
      (secondPoint P (NorthMeridianEvaluationPoint.opposite v₀)) =
    SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 0 ≫ SelfCutThomCocycle.selfEvaluation n := by
  have he : shortMap P v₀ k ≫ OrthogonalSphereEscape.pair (firstPoint P (NorthMeridianEvaluationPoint.opposite v₀))
      (secondPoint P (NorthMeridianEvaluationPoint.opposite v₀)) = OrthogonalSphereEscape.pair (first P v₀ k) (shortEnd P v₀ k) := by
    apply TopCat.ext
    intro z
    exact Prod.ext (ConcreteCategory.congr_hom (short_first P v₀ k) z)
      (ConcreteCategory.congr_hom (short_second P v₀ k) z)
  exact he.trans (NativeSameLegThomReduction.short_map P v₀ k)

theorem long_pair {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    longMap P v₀ k ≫ OrthogonalSphereEscape.pair (firstPoint P (NorthMeridianEvaluationPoint.opposite v₀))
      (secondPoint P (NorthMeridianEvaluationPoint.opposite v₀)) =
    SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 12 ≫ SelfCutThomCocycle.selfEvaluation n := by
  have he : longMap P v₀ k ≫ OrthogonalSphereEscape.pair (firstPoint P (NorthMeridianEvaluationPoint.opposite v₀))
      (secondPoint P (NorthMeridianEvaluationPoint.opposite v₀)) = OrthogonalSphereEscape.pair (first P v₀ k) (longEnd P v₀ k) := by
    apply TopCat.ext
    intro z
    exact Prod.ext (ConcreteCategory.congr_hom (long_first P v₀ k) z)
      (ConcreteCategory.congr_hom (long_second P v₀ k) z)
  exact he.trans (NativeSameLegThomReduction.long_map P v₀ k)

theorem short_seam {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : localSpace P v₀ k)
    (hz : z.val.2.down = 0) :
    shortMap P v₀ k z ∈ CommonMeridianThomSeamCorrection.diagonalSet P (NorthMeridianEvaluationPoint.opposite v₀) := by
  change z.val.1.1 = later z.val.1.1 z.val.2.down
  rw [hz, short_diagonal]

theorem long_seam {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : localSpace P v₀ k)
    (hz : z.val.2.down = 1) :
    longMap P v₀ k z ∈ CommonMeridianThomSeamCorrection.diagonalSet P (NorthMeridianEvaluationPoint.opposite v₀) := by
  change z.val.1.1 = earlier z.val.1.1 z.val.2.down
  rw [hz, long_diagonal]

end
end Finsler.NativeSameLegCommonMaps
