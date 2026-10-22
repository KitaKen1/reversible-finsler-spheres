module

public import Finsler.Loop.NativeUnitRelativeCriterion
public import Finsler.Loop.ConstantRelativeOutputCochain

/-! The exact remaining UNIT tests on ORIGINAL geometric time-cup
cochains at ANY admissible original radii. Every output is an actual
closed representative literally zero on constants, and represents
the correct relative output class. No desired vanishing is assumed. -/
@[expose] public section
namespace Finsler.NativeUnitOriginalCochain
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

def cochain : singularCochainGroup (ZMod 2) (Loops (m + 1)) ((m + m) + (m + 1)) :=
  GeometricTimeCupCochain.cochain m m hρ hρr hr (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))
    (m + 1) (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)

theorem closed : cochainCoboundary (ZMod 2) (Loops (m + 1)) ((m + m) + (m + 1)) (cochain m hρ hρr hr a) = 0 :=
  GeometricTimeCupCochain.closed m m hρ hρr hr _ (m + 1) _ (classRepr_isCocycle _ m _)
    (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a)

theorem cochain_class (hm : 1 ≤ m) :
    cocycleClass _ ((m + m) + (m + 1)) (cochain m hρ hρr hr a) (closed m hρ hρr hr a) =
      CanonicalGlobalTimeCup.product m m (m + 1) (MeridianLoopClass.H1TransgressionClass m)
        (ConstantRelativeOutputPairing.absolute (m + 1) (m + 1) a) := by
  have he := GlobalTimeCupCohomology.product_cocycle m hρ hρr hr m (m + 1)
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)
    (classRepr_isCocycle _ m _) (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a)
  have hb := ConstantRelativeOutputCochain.cochain_class (m + 1) (m + 1) a
  change cocycleClass (Loops (m + 1)) (m + 1) (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)
    (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a) = ConstantRelativeOutputPairing.absolute (m + 1) (m + 1) a at hb
  rw [cocycleClass_classRepr, hb] at he
  exact he.symm.trans (CanonicalGlobalTimeCup.product_compare m hm m (m + 1) hρ hρr hr _ _)

theorem original_pairing (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap _ ((m + m) + (m + 1))).hom
      (cocycleClass _ _ (cochain m hρ hρr hr a) (closed m hρ hρr hr a)) (MeridianThetaCutCoefficient.thetaInput m hm P v₀) =
      RelativeKronecker.comparison (fullPair (m + 1)) (m + 1) a (NativeConstantUnitDefect.relativeCut m hm P v₀) := by
  rw [cochain_class m hρ hρr hr a hm]
  exact (NativeUnitRelativeCriterion.relative_cut_pairing m hm P v₀ a).symm

theorem unit_iff_original_tests_zero (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeConstantUnitDefect.cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) ↔
      ∀ b : RelativeCup.cohomology (fullPair (m + 1)) (m + 1),
        (kroneckerMap _ ((m + m) + (m + 1))).hom
          (cocycleClass _ _ (cochain m hρ hρr hr b) (closed m hρ hρr hr b)) (MeridianThetaCutCoefficient.thetaInput m hm P v₀) = 0 := by
  rw [NativeUnitRelativeCriterion.unit_iff_all_relative_pairings_zero]
  simp only [original_pairing m hρ hρr hr _ hm P v₀]

end
end Finsler.NativeUnitOriginalCochain
