module

public import Finsler.Loop.MeridianRelativeSweep
public import Finsler.Loop.NorthMeridianEvaluationPoint

/-! The ORIGINAL localized normalized sphere top cocycle has literal
zero restriction to the REAL fixed-meridian curve. Its true relative
class pairs to ONE with the ACTUAL variable-meridian interval sweep.
This detects a single relative factor; no double-product or global
Theta coefficient is assigned a value here. -/
@[expose] public section
namespace Finsler.MeridianRelativeFundamental
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.MeridianRelativeSweep
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem restriction_zero {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    cochainPullback (pair P v₀).map n
      (LocalizedSphereTopCocycle.cocycle n hn (NorthMeridianEvaluationPoint.target P v₀) hη) = 0 := by
  apply NorthMeridianEvaluationPoint.cocycle_pullback_zero hn P v₀ hη hη2
  intro x
  obtain ⟨t, ht⟩ := x.property
  change (x.val : Sphere n) ∈ NorthMeridianEvaluationPoint.excluded P v₀
  rw [← ht]
  exact NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ t

def relativeCocycle {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) : RelativeCupCochain.relative (pair P v₀) n :=
  (RelativeCupCochain.exists_lift (pair P v₀) n
    (LocalizedSphereTopCocycle.cocycle n hn (NorthMeridianEvaluationPoint.target P v₀) hη)
    (restriction_zero hn P v₀ hη hη2)).choose

theorem toAmbient {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    RelativeCupCochain.toAmbient (pair P v₀) n (relativeCocycle hn P v₀ hη hη2) =
      LocalizedSphereTopCocycle.cocycle n hn (NorthMeridianEvaluationPoint.target P v₀) hη :=
  (RelativeCupCochain.exists_lift (pair P v₀) n
    (LocalizedSphereTopCocycle.cocycle n hn (NorthMeridianEvaluationPoint.target P v₀) hη)
    (restriction_zero hn P v₀ hη hη2)).choose_spec

theorem closed {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    RelativeCupCochain.differential (pair P v₀) n (relativeCocycle hn P v₀ hη hη2) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (pair P v₀) _
  rw [RelativeCupCochain.toAmbient_differential, toAmbient, map_zero]
  exact LocalizedSphereTopCocycle.closed n hn _ hη

def relativeClass {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) : RelativeCup.cohomology (pair P v₀) n :=
  CochainClass.classOf (RelativeCup.cx (pair P v₀)) n (relativeCocycle hn P v₀ hη hη2)
    (closed hn P v₀ hη hη2)

theorem original_top_class {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    (relativeToPool (pair P v₀) n).hom (relativeClass hn P v₀ hη hη2) =
      SphereTopClass.topClass n hn := by
  have he := RelativeCup.relativeToPool_classOf (pair P v₀) n
    (relativeCocycle hn P v₀ hη hη2) (closed hn P v₀ hη hη2)
  exact he.trans ((CochainClass.classOf_congr _ n (toAmbient hn P v₀ hη hη2) _ _).trans
    (LocalizedSphereTopCocycle.top_class n hn _ hη))

theorem pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    RelativeKronecker.comparison (pair P v₀) (m + 1)
      (relativeClass (by omega) P v₀ hη hη2) (image m hm P v₀) = 1 := by
  have he := congrArg (fun φ => φ (SphereUnitCandidate.fundamental (m + 1) (by omega)))
    (RelativeKronecker.fromRelative_comparison (pair P v₀) (m + 1)
      (relativeClass (by omega) P v₀ hη hη2))
  change RelativeKronecker.comparison (pair P v₀) (m + 1) (relativeClass (by omega) P v₀ hη hη2)
    (((pair P v₀).singularHomologyπ (ModuleCat.of (ZMod 2) (ZMod 2)) (m + 1)).hom
      (SphereUnitCandidate.fundamental (m + 1) (by omega))) = _ at he
  rw [original_top_class] at he
  rw [MeridianRelativeSweep.image_fundamental]
  exact he.trans (SphereUnitCandidate.top_evaluation_one (m + 1) (by omega))

theorem image_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    image m hm P v₀ ≠ 0 := by
  intro hz
  have he := pairing_one m hm P v₀ (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
  rw [hz, map_zero] at he
  exact zero_ne_one he

theorem relativeClass_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    relativeClass (by omega) P v₀ hη hη2 ≠ 0 := by
  intro hz
  have he := pairing_one m hm P v₀ hη hη2
  rw [hz, map_zero, LinearMap.zero_apply] at he
  exact zero_ne_one he

end
end Finsler.MeridianRelativeFundamental
