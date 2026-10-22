module

public import Finsler.Loop.NativeBVSingleWitness

/-! Discharge the first BV comparison with the ORIGINAL actual triple
meridian cube. Its pairing with the original GH square is forced to ONE
by actual rank one; no new generator or assumed coefficient is introduced. -/
@[expose] public section
namespace Finsler.NativePrimitiveBVComparison
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.NativeThetaBVShiftBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem cube_degree (m : ℕ) : 3 * m = NativeGHPowers.degree m 1 := by
  rw [NativeGHPowers.degree_formula]

def cube (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m 1) :=
  (eqToHom (congrArg (homologyZMod2 (Loops (m + 1))) (cube_degree m))).hom
    (MeridianRotationClasses.H1Cube m (by omega) P v₀)

private theorem BV_cast (n : ℕ) {i j : ℕ} (h : i = j) (z : homologyZMod2 (Loops n) i) :
    (eqToHom (congrArg (homologyZMod2 (Loops n)) (congrArg (fun k => k + 1) h))).hom
      ((H1LoopRotation.BV n i).hom z) =
    (H1LoopRotation.BV n j).hom ((eqToHom (congrArg (homologyZMod2 (Loops n)) h)).hom z) := by
  subst j
  rfl

private theorem cast_trans (X : TopCat.{0}) {i j k : ℕ} (h : i = j) (g : j = k)
    (z : homologyZMod2 X i) :
    (eqToHom (congrArg (homologyZMod2 X) g)).hom
      ((eqToHom (congrArg (homologyZMod2 X) h)).hom z) =
    (eqToHom (congrArg (homologyZMod2 X) (h.trans g))).hom z := by
  subst j
  subst k
  rfl

theorem aligned_cube (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) :
    alignedBV m 0 (cube m hm P v₀) = NativeThetaPowers.fullPower m hm F P v₀ 0 := by
  rw [NativeThetaPowers.full_zero]
  unfold alignedBV cube
  rw [← BV_cast (m + 1) (cube_degree m)]
  rw [cast_trans _ (congrArg (fun k => k + 1) (cube_degree m)) (degree_match m 0)]
  rfl

theorem cube_pairing_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m 1)).hom (NativeGHPowers.power m 1)
      (cube m hm P v₀) = 1 := by
  apply (NativeGHRankOne.nonzero_iff_pairing_one m hm P v₀ 1 _).mp
  intro hz
  have h := aligned_cube m hm (roundMetric (m + 1)) P v₀
  rw [hz, NativeBVSingleWitness.alignedBV_zero] at h
  exact NativeThetaPowers.fullPower_ne_zero m hm (roundMetric (m + 1)) P v₀ 0 h.symm

theorem primitive_detectsTheta (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) : detectsTheta m hm F P v₀ 0 := by
  apply NativeBVSingleWitness.detectsTheta_of_one_witness m hm F P v₀ 0 (cube m hm P v₀)
  rw [aligned_cube]
  exact NativeThetaPowers.fullPower_ne_zero m hm F P v₀ 0

theorem primitive_lift_above_square (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) {a : ℝ} (ha : NativeGHSpectralSupport.level m F 1 < a) :
    a ∈ NativeThetaSpectralLength.lifts m hm F P v₀ 0 :=
  lift_above_of_BV m hm F P v₀ 0 (primitive_detectsTheta m hm F P v₀) ha

theorem primitive_le_square (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeThetaSpectralLength.level m hm F P v₀ 0 ≤ NativeGHSpectralSupport.level m F 1 :=
  level_le_of_BV m hm F P v₀ 0 (primitive_detectsTheta m hm F P v₀)

theorem rate_sandwich (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeThetaSpectralLength.level m hm F P v₀ 0 / 2 ≤ NativeGHOptimalRate.rate m F ∧
      NativeGHOptimalRate.rate m F ≤ NativeThetaSpectralLength.level m hm F P v₀ 0 := by
  constructor
  · have h := NativeGHOptimalRate.average_le_rate m hm F P v₀ 1
    norm_num [NativeGHOptimalRate.average] at h
    linarith [primitive_le_square m hm F P v₀]
  · exact NativeThetaSpectralLength.rate_le_primitive_level m hm F P v₀

end
end Finsler.NativePrimitiveBVComparison
