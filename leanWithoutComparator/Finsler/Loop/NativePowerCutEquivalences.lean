module

public import Finsler.Loop.NativePrimitiveBVComparison

/-! The ORIGINAL primitive self-cut is a linear equivalence on both
original GH-input and Theta-output towers. No BV commutation is assumed. -/
@[expose] public section
namespace Finsler.NativePowerCutEquivalences
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def ghCut (m r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) →ₗ[ZMod 2]
    homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r) :=
  (CanonicalGlobalSelfCut.map m m (NativeGHPowers.degree m r) (MeridianLoopClass.H1TransgressionClass m)).hom

def thetaCut (m r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m (r + 1)) →ₗ[ZMod 2]
    homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) :=
  (CanonicalGlobalSelfCut.map m m (NativeThetaPowers.degree m r) (MeridianLoopClass.H1TransgressionClass m)).hom

theorem gh_pairing (m r : ℕ) (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))) :
    (kroneckerMap _ (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) (ghCut m r z) =
      (kroneckerMap _ (NativeGHPowers.degree m (r + 1))).hom (NativeGHPowers.power m (r + 1)) z :=
  CanonicalGlobalSelfCut.pairing m m (NativeGHPowers.degree m r) _ _ z

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

include hm P v₀ in
theorem gh_injective (r : ℕ) : Function.Injective (ghCut m r) := by
  intro a b hab
  apply NativeGHRankOne.pairing_injective m hm P v₀ (r + 1)
  rw [← gh_pairing, ← gh_pairing, hab]

include hm F P v₀ in
theorem gh_surjective (r : ℕ) : Function.Surjective (ghCut m r) :=
  NativePrimitiveCutSurjective.map_surjective m hm F P v₀ (NativeGHPowers.degree m r)

def ghEquiv (r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) ≃ₗ[ZMod 2]
    homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r) :=
  LinearEquiv.ofBijective (ghCut m r) ⟨gh_injective m hm P v₀ r, gh_surjective m hm F P v₀ r⟩

omit F in
theorem gh_detector (r : ℕ) :
    ghCut m r (NativeGHRankOne.detector m hm P v₀ (r + 1)) = NativeGHRankOne.detector m hm P v₀ r := by
  apply NativeGHRankOne.pairing_injective m hm P v₀ r
  rw [gh_pairing, NativeGHRankOne.detector_pairing, NativeGHRankOne.detector_pairing]

theorem theta_full (r : ℕ) :
    thetaCut m r (NativeThetaPowers.fullPower m hm F P v₀ (r + 1)) =
      NativeThetaPowers.fullPower m hm F P v₀ r := NativeThetaPowers.full_succ_cut m hm F P v₀ r

include hm F P v₀ in
theorem theta_injective (r : ℕ) : Function.Injective (thetaCut m r) := by
  intro a b hab
  apply sub_eq_zero.mp
  by_contra hz
  have he := NativeThetaRankOne.nonzero_eq_theta m hm F P v₀ (r + 1) (a - b) hz
  have h := congrArg (thetaCut m r) he
  rw [map_sub, hab, sub_self, theta_full] at h
  exact NativeThetaPowers.fullPower_ne_zero m hm F P v₀ r h.symm

include hm F P v₀ in
theorem theta_surjective (r : ℕ) : Function.Surjective (thetaCut m r) :=
  NativePrimitiveCutSurjective.map_surjective m hm F P v₀ (NativeThetaPowers.degree m r)

def thetaEquiv (r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m (r + 1)) ≃ₗ[ZMod 2]
    homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) :=
  LinearEquiv.ofBijective (thetaCut m r) ⟨theta_injective m hm F P v₀ r, theta_surjective m hm F P v₀ r⟩

end
end Finsler.NativePowerCutEquivalences
