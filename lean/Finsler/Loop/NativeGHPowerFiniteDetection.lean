module

public import Finsler.Loop.NativeGHPowerLengthDetection
public import Finsler.Loop.NativeFilteredRelativeTheta

/-! The SAME genuine relative GH powers remain nonzero in ACTUAL
finite strict-length/constant-loop pairs with a LINEAR length bound.
Actual pair maps, quotient naturality and the actual relative
Kronecker comparison identify their detectors with the full ones. -/
@[expose] public section
namespace Finsler.NativeGHPowerFiniteDetection
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem quotient_full {n : ℕ} (F : ReversibleMetric n) (B : ℝ) (k : ℕ)
    (z : homologyZMod2 (lengthSpace F B) k) :
    ((NativeFilteredRelativeTheta.pair F B).singularHomologyMap
      (NativeFilteredRelativeTheta.pairMap F B) coeff k).hom
        (((NativeFilteredRelativeTheta.pair F B).singularHomologyπ coeff k).hom z) =
    ConstantRelativePairing.homologyToRelative n k
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F B) k).hom z) := by
  have h := (NativeFilteredRelativeTheta.quotient_natural
    (NativeFilteredRelativeTheta.pairMap F B) k z).symm
  have hf : TopPair.Hom.fst (NativeFilteredRelativeTheta.pairMap F B) =
      LengthFilteredLoopRotation.full F B ≫ FullLoopModel.insert n := rfl
  rw [hf, ← push_comp_apply] at h
  exact h

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def finitePower (B : ℝ) (r : ℕ) :
    RelativeCup.cohomology (NativeFilteredRelativeTheta.pair F B) (NativeGHPowers.degree m r) :=
  (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (NativeFilteredRelativeTheta.pairMap F B) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.relativePower m hm r)

theorem pairing (B : ℝ) (r : ℕ)
    (z : homologyZMod2 (lengthSpace F B) (NativeGHPowers.degree m r)) :
    RelativeKronecker.comparison (NativeFilteredRelativeTheta.pair F B) (NativeGHPowers.degree m r)
      (finitePower m hm F B r)
      (((NativeFilteredRelativeTheta.pair F B).singularHomologyπ coeff (NativeGHPowers.degree m r)).hom z) =
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F B) (NativeGHPowers.degree m r)).hom z) := by
  have hn := congrArg
    (fun φ => φ (((NativeFilteredRelativeTheta.pair F B).singularHomologyπ coeff
      (NativeGHPowers.degree m r)).hom z))
    (RelativeKronecker.naturality (NativeFilteredRelativeTheta.pairMap F B)
      (NativeGHPowers.degree m r) (NativeGHPowers.relativePower m hm r))
  change RelativeKronecker.comparison (NativeFilteredRelativeTheta.pair F B) (NativeGHPowers.degree m r)
      (finitePower m hm F B r)
      (((NativeFilteredRelativeTheta.pair F B).singularHomologyπ coeff (NativeGHPowers.degree m r)).hom z) =
    RelativeKronecker.comparison (fullPair (m + 1)) (NativeGHPowers.degree m r)
      (NativeGHPowers.relativePower m hm r)
      (((NativeFilteredRelativeTheta.pair F B).singularHomologyMap
        (NativeFilteredRelativeTheta.pairMap F B) coeff (NativeGHPowers.degree m r)).hom
          (((NativeFilteredRelativeTheta.pair F B).singularHomologyπ coeff (NativeGHPowers.degree m r)).hom z)) at hn
  exact hn.trans ((congrArg
    (RelativeKronecker.comparison (fullPair (m + 1)) (NativeGHPowers.degree m r)
      (NativeGHPowers.relativePower m hm r))
    (quotient_full F B (NativeGHPowers.degree m r) z)).trans
      (NativeGHPowerLengthDetection.relative_pairing m hm r _))

variable (P : Sphere (m + 1)) (v₀ : equator P)

theorem exists_linear_pairing :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ r : ℕ,
      ∃ z : homologyZMod2 (lengthSpace F
        (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1))) (NativeGHPowers.degree m r),
        RelativeKronecker.comparison
          (NativeFilteredRelativeTheta.pair F (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1)))
          (NativeGHPowers.degree m r)
          (finitePower m hm F (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1)) r)
          (((NativeFilteredRelativeTheta.pair F
            (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1))).singularHomologyπ coeff
              (NativeGHPowers.degree m r)).hom z) = 1 := by
  obtain ⟨b₀, hb₀, h⟩ := NativeGHPowerLengthDetection.exists_linear_detection m hm F P v₀
  refine ⟨b₀, hb₀, ?_⟩
  intro r
  obtain ⟨z, hz⟩ := h r
  exact ⟨z, (pairing m hm F _ r z).trans hz⟩

theorem exists_linear_nonzero :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ r : ℕ,
      finitePower m hm F (b₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1)) r ≠ 0 := by
  obtain ⟨b₀, hb₀, h⟩ := exists_linear_pairing m hm F P v₀
  refine ⟨b₀, hb₀, ?_⟩
  intro r hz
  obtain ⟨z, hpair⟩ := h r
  rw [hz, map_zero, LinearMap.zero_apply] at hpair
  exact zero_ne_one hpair

end
end Finsler.NativeGHPowerFiniteDetection
