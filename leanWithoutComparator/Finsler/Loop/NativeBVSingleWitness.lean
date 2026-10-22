module

public import Finsler.Loop.NativeGHRankOne
public import Finsler.Loop.NativeThetaBVNonzeroCriterion

/-! Every original GH detector is the same full homology class.
Thus one nonzero actual BV image suffices for the SAME Theta identification. -/
@[expose] public section
namespace Finsler.NativeBVSingleWitness
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.NativeThetaBVShiftBridge
open Finsler.NativeThetaBVNonzeroCriterion
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem alignedBV_zero (m r : ℕ) : alignedBV m r 0 = 0 := by
  unfold alignedBV
  rw [map_zero, map_zero]

theorem nonzero_iff_one_witness (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    nonzeroOnDetectors m r ↔
      ∃ z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)), alignedBV m r z ≠ 0 := by
  constructor
  · intro h
    exact ⟨NativeGHRankOne.detector m hm P v₀ (r + 1), h _ (NativeGHRankOne.detector_pairing m hm P v₀ (r + 1))⟩
  · rintro ⟨z, hz⟩ w hw
    have hn : z ≠ 0 := by intro h; rw [h, alignedBV_zero] at hz; exact hz rfl
    have he : w = z := NativeGHRankOne.pairing_injective m hm P v₀ (r + 1)
      (hw.trans ((NativeGHRankOne.nonzero_iff_pairing_one m hm P v₀ (r + 1) z).mp hn).symm)
    rw [he]
    exact hz

theorem detectsTheta_of_one_witness (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))) (hz : alignedBV m r z ≠ 0) :
    detectsTheta m hm F P v₀ r :=
  (detectsTheta_iff_nonzero m hm F P v₀ r).mpr
    ((nonzero_iff_one_witness m hm P v₀ r).mpr ⟨z, hz⟩)

theorem level_le_of_one_witness (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))) (hz : alignedBV m r z ≠ 0) :
    NativeThetaSpectralLength.level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + 1) :=
  level_le_of_BV m hm F P v₀ r (detectsTheta_of_one_witness m hm F P v₀ r z hz)

theorem gap_le_of_alternating_witnesses (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P)
    (h : ∀ r, (∃ z, alignedBV m r z ≠ 0) ∨ (∃ z, alignedBV m (r + 1) z ≠ 0)) (r : ℕ) :
    NativeThetaGHSpectralGap.gap m hm F P v₀ r ≤ 2 * NativeThetaSpectralLength.level m hm F P v₀ 0 := by
  apply gap_le_of_alternating_nonzero m hm F P v₀ _ r
  intro j
  exact (h j).imp ((nonzero_iff_one_witness m hm P v₀ j).mpr)
    ((nonzero_iff_one_witness m hm P v₀ (j + 1)).mpr)

end
end Finsler.NativeBVSingleWitness
