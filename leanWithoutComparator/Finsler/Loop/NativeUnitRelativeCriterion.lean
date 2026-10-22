module

public import Finsler.Loop.NativeConstantUnitDefect
public import Finsler.Loop.ConstantRelativeOutputPairing

/-! Exact UNIT target for the ORIGINAL operation: it suffices and is
necessary that original Theta kill ALL true relative output classes.
The output restriction is actual constant-relative cohomology, and
the input operation is the original canonical time cup. A single
evaluation top-class pairing is deliberately not substituted for it. -/
@[expose] public section
namespace Finsler.NativeUnitRelativeCriterion
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

theorem relative_cut_pairing (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1)) :
    RelativeKronecker.comparison (fullPair (m + 1)) (m + 1) a (NativeConstantUnitDefect.relativeCut m hm P v₀) =
      (kroneckerMap _ ((m + m) + (m + 1))).hom
        (CanonicalGlobalTimeCup.product m m (m + 1) (MeridianLoopClass.H1TransgressionClass m)
          (ConstantRelativeOutputPairing.absolute (m + 1) (m + 1) a)) (MeridianThetaCutCoefficient.thetaInput m hm P v₀) := by
  rw [NativeConstantUnitDefect.relativeCut, ConstantRelativeOutputPairing.pairing]
  exact CanonicalGlobalSelfCut.pairing m m (m + 1) _ _ _

theorem unit_iff_all_relative_pairings_zero :
    NativeConstantUnitDefect.cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) ↔
      ∀ a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1),
        RelativeKronecker.comparison (fullPair (m + 1)) (m + 1) a (NativeConstantUnitDefect.relativeCut m hm P v₀) = 0 := by
  rw [NativeConstantUnitDefect.unit_iff_relative_zero, ConstantRelativeOutputPairing.relative_zero_iff]

theorem unit_iff_original_timecup_tests_zero :
    NativeConstantUnitDefect.cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) ↔
      ∀ a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1),
        (kroneckerMap _ ((m + m) + (m + 1))).hom
          (CanonicalGlobalTimeCup.product m m (m + 1) (MeridianLoopClass.H1TransgressionClass m)
            (ConstantRelativeOutputPairing.absolute (m + 1) (m + 1) a)) (MeridianThetaCutCoefficient.thetaInput m hm P v₀) = 0 := by
  rw [unit_iff_all_relative_pairings_zero]
  simp only [relative_cut_pairing]

end
end Finsler.NativeUnitRelativeCriterion
