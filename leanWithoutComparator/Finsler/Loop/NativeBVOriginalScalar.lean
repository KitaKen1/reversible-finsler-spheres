module

public import Finsler.Loop.NativePrimitiveBVComparison
public import Finsler.Loop.NativeHighPowerUnit

/-! Coordinates for actual BV using the SAME original GH evaluation test.
The scalar is an actual pairing, not an assumed parity coefficient. -/
@[expose] public section
namespace Finsler.NativeBVOriginalScalar
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.NativeThetaBVShiftBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def thetaPairing (m r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) →ₗ[ZMod 2] ZMod 2 :=
  (kroneckerMap _ (NativeThetaPowers.degree m r)).hom (NativeHighPowerUnitComparison.ghEvaluationTest m r)

def BVmap (m r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) →ₗ[ZMod 2]
    homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) :=
  (eqToHom (congrArg (homologyZMod2 (Loops (m + 1))) (degree_match m r))).hom.comp
    (H1LoopRotation.BV (m + 1) (NativeGHPowers.degree m (r + 1))).hom

def coefficient (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) : ZMod 2 :=
  thetaPairing m r (alignedBV m r (NativeGHRankOne.detector m hm P v₀ (r + 1)))

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem theta_expansion (r : ℕ) (z : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r)) :
    z = thetaPairing m r z • NativeThetaPowers.fullPower m hm F P v₀ r := by
  obtain ⟨c, hc⟩ := NativeThetaRankOne.theta_spans m hm F P v₀ r z
  rw [← hc, map_smul]
  have he : thetaPairing m r (NativeThetaPowers.fullPower m hm F P v₀ r) = 1 :=
    NativeHighPowerUnit.scalar_one m hm F P v₀ r
  rw [he]
  simp

include hm F P v₀ in
theorem thetaPairing_injective (r : ℕ) : Function.Injective (thetaPairing m r) := by
  intro a b h
  rw [theta_expansion m hm F P v₀ r a, theta_expansion m hm F P v₀ r b, h]

omit F in
theorem gh_expansion (r : ℕ) (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r)) :
    z = ((kroneckerMap _ (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) z) •
      NativeGHRankOne.detector m hm P v₀ r := by
  apply NativeGHRankOne.pairing_injective m hm P v₀ r
  rw [map_smul, NativeGHRankOne.detector_pairing]
  exact (mul_one _).symm

theorem BV_formula (r : ℕ) (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))) :
    alignedBV m r z =
      (((kroneckerMap _ (NativeGHPowers.degree m (r + 1))).hom (NativeGHPowers.power m (r + 1)) z) *
        coefficient m hm P v₀ r) • NativeThetaPowers.fullPower m hm F P v₀ r := by
  change BVmap m r z = _
  conv_lhs => rw [gh_expansion m hm P v₀ (r + 1) z]
  rw [map_smul]
  have he := theta_expansion m hm F P v₀ r (BVmap m r (NativeGHRankOne.detector m hm P v₀ (r + 1)))
  rw [he, smul_smul]
  rfl

omit F in
theorem coefficient_independent (Q : Sphere (m + 1)) (w₀ : equator Q) (r : ℕ) :
    coefficient m hm Q w₀ r = coefficient m hm P v₀ r := by
  have he : NativeGHRankOne.detector m hm Q w₀ (r + 1) = NativeGHRankOne.detector m hm P v₀ (r + 1) :=
    NativeGHRankOne.pairing_injective m hm P v₀ (r + 1)
      ((NativeGHRankOne.detector_pairing m hm Q w₀ (r + 1)).trans
        (NativeGHRankOne.detector_pairing m hm P v₀ (r + 1)).symm)
  unfold coefficient
  rw [he]

omit F in
theorem coefficient_zero : coefficient m hm P v₀ 0 = 1 := by
  have he : NativeGHRankOne.detector m hm P v₀ 1 = NativePrimitiveBVComparison.cube m hm P v₀ :=
    NativeGHRankOne.pairing_injective m hm P v₀ 1
      ((NativeGHRankOne.detector_pairing m hm P v₀ 1).trans
        (NativePrimitiveBVComparison.cube_pairing_one m hm P v₀).symm)
  unfold coefficient
  rw [he, NativePrimitiveBVComparison.aligned_cube m hm (roundMetric (m + 1)) P v₀]
  exact NativeHighPowerUnit.scalar_one m hm (roundMetric (m + 1)) P v₀ 0

theorem coefficient_one_iff (r : ℕ) : coefficient m hm P v₀ r = 1 ↔ detectsTheta m hm F P v₀ r := by
  constructor
  · intro h z hz
    rw [BV_formula m hm F P v₀ r z, hz, h, one_mul, one_smul]
  · intro h
    have he := congrArg (thetaPairing m r)
      (h (NativeGHRankOne.detector m hm P v₀ (r + 1)) (NativeGHRankOne.detector_pairing m hm P v₀ (r + 1)))
    exact he.trans (NativeHighPowerUnit.scalar_one m hm F P v₀ r)

end
end Finsler.NativeBVOriginalScalar
