module

public import Finsler.Loop.NativeBVEvaluationAnnihilation

/-! UNCONDITIONAL original BV coefficient ONE for EVERY n>=3. The
ordinary GH remainder vanishes; the evaluation-cup second term vanishes
on the ACTUAL punctured patch which generates the target homology.
The SAME original GH detectors and length-preserving BV give shift ONE,
a power-independent gap, and SAME cut representatives with full UNIT
image. Finite-level UF equality and full HR remain separate. -/
@[expose] public section
namespace Finsler.NativeBVFixedShift
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

include F in
theorem coefficient_one (r : ℕ) : NativeBVOriginalScalar.coefficient m hm P v₀ r = 1 := by
  obtain ⟨c, hc⟩ := ((ModuleCat.epi_iff_surjective
    ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1)))).mp inferInstance)
      (NativeRaisedBVCandidates.full m hm F P v₀ r)
  have he := NativeBVSourceCupProjection.coefficient_on_cycle m hm F r P v₀ c hc
  have ht : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      NativeBVSourceCupProjection.test m hm F r =
      (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        NativeSourceGHProjection.ordinaryCup m hm F r := by
    rw [NativeBVOrdinaryCupRotation.formula, Preadditive.comp_add,
      NativeBVOrdinaryCupRotation.firstTerm_cycle_values,
      NativeBVEvaluationAnnihilation.secondTerm_cycles_zero m hm F r P v₀, add_zero]
  rw [ht] at he
  have hv := NativeSourceGHProjection.value_one_plus_remainder m hm F r P v₀ c hc
  rw [NativeOrdinaryGHCupVanishing.remainder_cycles_zero m hm F r P v₀] at hv
  exact he.trans (hv.trans (add_zero _))

theorem detectsTheta (r : ℕ) : NativeThetaBVShiftBridge.detectsTheta m hm F P v₀ r :=
  (NativeBVOriginalScalar.coefficient_one_iff m hm F P v₀ r).mp (coefficient_one m hm F P v₀ r)

theorem raised_BV (r : ℕ) : NativeThetaBVShiftBridge.alignedBV m r (NativeRaisedBVCandidates.full m hm F P v₀ r) =
    NativeThetaPowers.fullPower m hm F P v₀ r :=
  detectsTheta m hm F P v₀ r _ (NativeRaisedBVCandidates.pairing_one m hm F P v₀ r)

theorem original_BV_formula (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))) :
    NativeThetaBVShiftBridge.alignedBV m r z =
      ((kroneckerMap _ (NativeGHPowers.degree m (r + 1))).hom (NativeGHPowers.power m (r + 1)) z) •
        NativeThetaPowers.fullPower m hm F P v₀ r := by
  rw [NativeBVOriginalScalar.BV_formula m hm F P v₀, coefficient_one m hm F P v₀, mul_one]

theorem lift_above_next_support (r : ℕ) {a : ℝ} (ha : NativeGHSpectralSupport.level m F (r + 1) < a) :
    a ∈ NativeThetaSpectralLength.lifts m hm F P v₀ r :=
  NativeThetaBVShiftBridge.lift_above_of_BV m hm F P v₀ r (detectsTheta m hm F P v₀ r) ha

theorem shift_one (r : ℕ) : NativeThetaSpectralLength.level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + 1) :=
  NativeThetaBVShiftBridge.level_le_of_BV m hm F P v₀ r (detectsTheta m hm F P v₀ r)

theorem uniform_gap (r : ℕ) : NativeThetaGHSpectralGap.gap m hm F P v₀ r ≤ NativeThetaSpectralLength.level m hm F P v₀ 0 := by
  have h := NativeThetaGHShiftShortcut.gap_le_of_shift m hm F P v₀ 1 (shift_one m hm F P v₀) r
  simpa only [Nat.cast_one, one_mul] using h

theorem uniform_same_cut : ∀ (r : ℕ) (δ : ℝ), 0 < δ →
    ∃ w : homologyZMod2 (lengthSpace F (NativeThetaSpectralLength.level m hm F P v₀ 0 + δ)) (m + 1),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F
        (NativeThetaSpectralLength.level m hm F P v₀ 0 + δ)) (m + 1)).hom w =
        NativeHighPowerUnitComparison.singleCut m hm F P v₀ r ∧
      (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
        ((homologyPushZMod2 (LengthFilteredLoopRotation.full F
          (NativeThetaSpectralLength.level m hm F P v₀ 0 + δ)) (m + 1)).hom w) =
        AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  NativeThetaGHSpectralGap.uniform_cut_of_gap_bound m hm F P v₀ (uniform_gap m hm F P v₀)

end
end Finsler.NativeBVFixedShift
