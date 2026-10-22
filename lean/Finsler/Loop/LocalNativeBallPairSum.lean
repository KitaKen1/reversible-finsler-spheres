module

public import Finsler.Loop.LocalNativeBallSlice

/-! On the WHOLE actual two-ball product the two ORIGINAL ordinary
tested/retained transgressions sum to the remaining primitive. The
real product contraction and the OLD exact diagonal-slice sum prove
this without a new whole-tube rejoining construction. Relative
supported-cap/complement corrections remain separate. -/
@[expose] public section
namespace Finsler.LocalNativeBallPairSum
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem slice_sum {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (LocalNativeBallCut.testedSlice P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (LocalNativeBallCut.retainedSlice P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a) := by
  have he := congrArg
    (cohPullback (NativeMatchingTestedPairing.middleSlice P (LocalNativeBallSlice.centerTime P v₀)
      (LocalNativeBallSlice.centerDirection P v₀)) q).hom
    (NativeMatchingTransgression.original_tested_retained_sum P v₀ b q a)
  rw [map_add, ← NativeMatchingTransgression.pullback_comp, ← NativeMatchingTransgression.pullback_comp,
    ← NativeMatchingTransgression.pullback_comp, NativeMatchingTestedPairing.middle_remaining] at he
  rw [LocalNativeBallSlice.testedSlice_matching, LocalNativeBallSlice.retainedSlice_matching]
  exact he

theorem whole_ball_sum {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (LocalNativeBallCut.tested P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (LocalNativeBallCut.retained P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P))) q).hom
        ((cohPullback (ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a)) := by
  rw [LocalNativeBallCut.tested_reduced, LocalNativeBallCut.retained_reduced, ← map_add, slice_sum]

end
end Finsler.LocalNativeBallPairSum
