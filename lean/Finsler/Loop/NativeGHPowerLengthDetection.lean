module

public import Finsler.Loop.NativeGHPowers

/-! Actual homology detectors for the actual right-associated GH
powers, inside genuine Finsler strict length cuts with a LINEAR
bound in the number of factors. Both absolute and original
constant-relative pairings are ONE. This is an upper bound on
detection lengths, not positive HR or full uniform filling. -/
@[expose] public section
namespace Finsler.NativeGHPowerLengthDetection
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem degree_ne_sphere (m : ℕ) (hm : 2 ≤ m) (r : ℕ) :
    NativeGHPowers.degree m r ≠ m + 1 := by
  cases r with
  | zero => change m ≠ m + 1; omega
  | succ r =>
    change (m + m) + NativeGHPowers.degree m r ≠ m + 1
    have hd := NativeGHPowers.degree_ge m r
    omega

theorem power_restriction_zero (m : ℕ) (hm : 2 ≤ m) (r : ℕ) :
    (cohPullback (SupportedCap.subspaceMap (Loops (m + 1)) (consts (m + 1)))
      (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 :=
  ConstantRelativeLift.restriction_zero (m + 1) (NativeGHPowers.degree m r)
    (by have hd := NativeGHPowers.degree_ge m r; omega) (degree_ne_sphere m hm r) _

theorem relative_pairing (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r)) :
    RelativeKronecker.comparison (fullPair (m + 1)) (NativeGHPowers.degree m r)
      (NativeGHPowers.relativePower m hm r)
      (ConstantRelativePairing.homologyToRelative (m + 1) (NativeGHPowers.degree m r) z) =
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) z := by
  have ha : FullRelativeSplit.absolute (m + 1) (NativeGHPowers.degree m r)
      (NativeGHPowers.relativePower m hm r) = NativeGHPowers.power m r :=
    NativeGHPowers.relativePower_absolute m hm r
  have hl := FullRelativeSplit.lift_absolute (m + 1) (NativeGHPowers.degree m r)
    (NativeGHPowers.relativePower m hm r)
  rw [ha] at hl
  rw [← hl]
  exact FullRelativeSplit.pairing (m + 1) (NativeGHPowers.degree m r)
    (NativeGHPowers.power m r) (power_restriction_zero m hm r) z

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

include hm in
theorem exists_linear_detection :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ r : ℕ,
      ∃ z : homologyZMod2 (lengthSpace F
        (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1))) (NativeGHPowers.degree m r),
        (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
          ((homologyPushZMod2 (LengthFilteredLoopRotation.full F
            (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1)))
              (NativeGHPowers.degree m r)).hom z) = 1 := by
  obtain ⟨b₀, hb₀, z₀, hz₀⟩ := NativePrimitiveCutSurjective.exists_positive_length_lift F m
    (MeridianLoopClass.H1Class m (by omega) P v₀)
  refine ⟨b₀, hb₀, ?_⟩
  intro r
  induction r with
  | zero =>
    refine ⟨(homologyPushZMod2 (LengthFilteredLoopRotation.cut F
      (by norm_num : b₀ ≤ b₀ + ((0 : ℕ) : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1))) m).hom z₀, ?_⟩
    have hcut := NativePrimitiveCutSurjective.cut_full_apply F
      (by norm_num : b₀ ≤ b₀ + ((0 : ℕ) : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1)) m z₀
    exact (congrArg ((kroneckerMap (Loops (m + 1)) m).hom (MeridianLoopClass.H1TransgressionClass m))
      hcut).trans
      ((congrArg ((kroneckerMap (Loops (m + 1)) m).hom (MeridianLoopClass.H1TransgressionClass m))
        hz₀).trans (MeridianPrimitiveNonzero.H1_pairing_one m (by omega) P v₀))
  | succ r ih =>
    obtain ⟨z, hz⟩ := ih
    let q := b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1)
    have hc : 0 < NativeThetaLengthCut.bound F P v₀ + 1 := by
      linarith [NativeThetaLengthCut.bound_positive F P v₀]
    have hq : 0 < q := by
      have ht := mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) hc.le
      dsimp only [q]
      linarith
    have he : NativeThetaLengthCut.bound F P v₀ + (q + 1) =
        b₀ + ((r + 1 : ℕ) : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1) := by
      dsimp only [q]
      push_cast
      ring
    refine ⟨(homologyPushZMod2 (LengthFilteredLoopRotation.cut F he.le)
      (NativeGHPowers.degree m (r + 1))).hom
        (NativePrimitiveCutSurjective.raised m hm F P v₀ q (by norm_num : (0 : ℝ) < 1)
          (NativeGHPowers.degree m r) z), ?_⟩
    rw [NativePrimitiveCutSurjective.cut_full_apply]
    have hd := NativePrimitiveCutSurjective.raised_cut_full m hm F P v₀ q hq (by norm_num : (0 : ℝ) < 1)
      (NativeGHPowers.degree m r) z
    have hp := CanonicalGlobalSelfCut.pairing m m (NativeGHPowers.degree m r)
      (MeridianLoopClass.H1TransgressionClass m) (NativeGHPowers.power m r)
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F
        (NativeThetaLengthCut.bound F P v₀ + (q + 1))) ((m + m) + NativeGHPowers.degree m r)).hom
        (NativePrimitiveCutSurjective.raised m hm F P v₀ q (by norm_num : (0 : ℝ) < 1)
          (NativeGHPowers.degree m r) z))
    exact hp.symm.trans ((congrArg
      ((kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)) hd).trans hz)

theorem exists_linear_relative_detection :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ r : ℕ,
      ∃ z : homologyZMod2 (lengthSpace F
        (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1))) (NativeGHPowers.degree m r),
        RelativeKronecker.comparison (fullPair (m + 1)) (NativeGHPowers.degree m r)
          (NativeGHPowers.relativePower m hm r)
          (ConstantRelativePairing.homologyToRelative (m + 1) (NativeGHPowers.degree m r)
            ((homologyPushZMod2 (LengthFilteredLoopRotation.full F
              (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1)))
                (NativeGHPowers.degree m r)).hom z)) = 1 := by
  obtain ⟨b₀, hb₀, h⟩ := exists_linear_detection m hm F P v₀
  refine ⟨b₀, hb₀, ?_⟩
  intro r
  obtain ⟨z, hz⟩ := h r
  exact ⟨z, (relative_pairing m hm r _).trans hz⟩

end
end Finsler.NativeGHPowerLengthDetection
