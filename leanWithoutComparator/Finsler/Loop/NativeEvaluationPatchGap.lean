module

public import Finsler.Loop.H1PuncturedPatchHomology
public import Finsler.Loop.NativeEvaluationMayerVietoris

/-! Supply the ACTUAL two patch-image zeros from the genuine
degree-n based-loop homology gaps. Together with the actual joint
overlap test these feed the EXISTING UNIT. Both geometric inputs
remain explicit pending obligations, not axioms or asserted facts. -/
@[expose] public section
namespace Finsler.NativeEvaluationPatchGap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.H1LocalFiber (based)
open Finsler.MeridianLoopFamily Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem fromPatches_zero_of_based {n : ℕ} (y : Sphere n) (k : ℕ)
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) k))
    (hS : IsZero (homologyZMod2 (TopCat.of (based (antipode y))) k)) :
    fromPatches y k = 0 := by
  have hu := H1PuncturedPatchHomology.fullDomain_homology_zero_of_based y k hN
  have hv := H1PuncturedPatchHomology.fullDomain_homology_zero_of_based (antipode y) k hS
  apply biprod.hom_ext'
  · exact hu.eq_of_src _ _
  · exact hv.eq_of_src _ _

theorem original_UNIT_of_based_gap_and_overlap (m : ℕ) (hm : 2 ≤ m) (y : Sphere (m + 1))
    (v₀ : equator y)
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1)))
    (hS : IsZero (homologyZMod2 (TopCat.of (based (antipode y))) (m + 1)))
    (ho : ∀ z : homologyZMod2 (overlap y) m,
      (homologyPushZMod2 (overlapEvaluation y) m).hom z = 0 → (toPatches y m).hom z = 0 → z = 0) :
    NativeConstantUnitDefect.cutFull m (by omega) y v₀ =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  original_UNIT_of_actual_cover_obligations m (by omega) y v₀
    (fromPatches_zero_of_based y (m + 1) hN hS) ho

theorem original_relativeCut_zero_of_based_gap_and_overlap (m : ℕ) (hm : 2 ≤ m) (y : Sphere (m + 1))
    (v₀ : equator y)
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1)))
    (hS : IsZero (homologyZMod2 (TopCat.of (based (antipode y))) (m + 1)))
    (ho : ∀ z : homologyZMod2 (overlap y) m,
      (homologyPushZMod2 (overlapEvaluation y) m).hom z = 0 → (toPatches y m).hom z = 0 → z = 0) :
    NativeConstantUnitDefect.relativeCut m (by omega) y v₀ = 0 :=
  (NativeConstantUnitDefect.unit_iff_relative_zero m (by omega) y v₀).mp
    (original_UNIT_of_based_gap_and_overlap m hm y v₀ hN hS ho)

end
end Finsler.NativeEvaluationPatchGap
