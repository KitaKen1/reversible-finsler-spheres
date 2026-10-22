module

public import Finsler.Loop.CompactSingleCutLengthOscillation
public import Finsler.Loop.OriginalFirstHalfFactorwiseCover

/-! One actual metric tester-oscillation scale precedes all tested
cochains and thresholds, and works for every smaller common scale. -/

@[expose] public section
namespace Finsler.SingleInputCutMetricAdequacy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev

noncomputable section
set_option autoImplicit false

variable {P : Type} [PseudoMetricSpace P] {n : ℕ}
  (α : C(P, SphereLoop n)) (r : ℝ) (hr : r < 1) (F : ReversibleMetric n) (ε σ : ℝ)

def Adequate : Prop := ∀ (c : ClosedInterval × P) (z w : CompactRotatedCutData.source α r),
  z.val ∈ OriginalFirstHalfFactorwiseCover.first σ c → w.val ∈ OriginalFirstHalfFactorwiseCover.first σ c →
  |SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr z) -
    SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr w)| < ε

theorem exists_scale [CompactSpace P] {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧ ∀ σ ≤ η, Adequate α r hr F ε σ := by
  obtain ⟨η, hη, hηb, hosc⟩ := CompactSingleCutLengthOscillation.exists_scale α r hr F hε hb
  refine ⟨η, hη, hηb, ?_⟩
  intro σ hση c z w hz hw
  apply hosc c z w
  · exact (show dist z.val c < σ from hz).trans_le hση
  · exact (show dist w.val c < σ from hw).trans_le hση

end
end Finsler.SingleInputCutMetricAdequacy
