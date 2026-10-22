module

public import Finsler.Loop.NativeThetaGHSpectralGap
public import Finsler.Loop.NativeThetaSpectralStep

/-! A fixed INDEX shift in a reverse Theta/GH comparison suffices for
a uniform LENGTH gap. The proof needs only the actual one-step Theta
bound, not product regrouping or endpoint-rate estimates. The shift
comparison is retained explicitly as an unproved geometric premise. -/
@[expose] public section
namespace Finsler.NativeThetaGHShiftShortcut
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
open Finsler.NativeThetaSpectralLength Finsler.NativeThetaGHSpectralGap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem level_shift_upper (r d : ℕ) :
    level m hm F P v₀ (r + d) ≤ level m hm F P v₀ r + (d : ℝ) * level m hm F P v₀ 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := NativeThetaSpectralStep.level_succ_upper m hm F P v₀ (r + d)
    rw [Nat.add_succ]
    push_cast
    linarith

theorem gap_le_of_shift (d : ℕ)
    (hshift : ∀ r, level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + d))
    (r : ℕ) : gap m hm F P v₀ r ≤ (d : ℝ) * level m hm F P v₀ 0 := by
  by_cases hdr : d ≤ r
  · have hi : r - d + d = r := Nat.sub_add_cancel hdr
    have h := level_shift_upper m hm F P v₀ (r - d) d
    have hs := hshift (r - d)
    rw [hi] at h hs
    dsimp [gap]
    linarith
  · have hrd : (r : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast (show r + 1 ≤ d by omega)
    have hb := mul_le_mul_of_nonneg_right hrd (level_positive m hm F P v₀ 0).le
    have ht := level_le_primitive_level m hm F P v₀ r
    obtain ⟨L, hLpos, hL⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
    have hs := NativeGHSpectralSupport.primitive_lower m hm F P v₀ r hL
    have hp : 0 < ((r : ℝ) + 1) * L := mul_pos (by positivity) hLpos
    dsimp [gap]
    linarith

theorem uniform_same_cut_of_shift (d : ℕ)
    (hshift : ∀ r, level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + d)) :
    ∀ (r : ℕ) (δ : ℝ), 0 < δ →
      ∃ w : homologyZMod2 (lengthSpace F ((d : ℝ) * level m hm F P v₀ 0 + δ)) (m + 1),
        (homologyPushZMod2 (LengthFilteredLoopRotation.full F
          ((d : ℝ) * level m hm F P v₀ 0 + δ)) (m + 1)).hom w =
          NativeHighPowerUnitComparison.singleCut m hm F P v₀ r ∧
        (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
          ((homologyPushZMod2 (LengthFilteredLoopRotation.full F
            ((d : ℝ) * level m hm F P v₀ 0 + δ)) (m + 1)).hom w) =
            AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  uniform_cut_of_gap_bound m hm F P v₀ (gap_le_of_shift m hm F P v₀ d hshift)

end
end Finsler.NativeThetaGHShiftShortcut
