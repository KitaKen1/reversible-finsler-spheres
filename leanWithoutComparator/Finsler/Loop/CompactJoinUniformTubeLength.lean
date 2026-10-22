module

public import Finsler.Loop.FullSecondHalfCompactTimeOperation

/-! The actual corrected-input and original time-family join budgets
hold on every smaller supplied tube, not just on an existentially
selected tube. This permits later common-radius selection. -/

@[expose] public section
namespace Finsler.CompactJoinUniformTubeLength

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SobolevLength

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] {n : ℕ} (F : ReversibleMetric n)
    (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ > 0, R₀ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R < 1), R ≤ R₀ →
      (∀ z : OriginalSecondHalfCompactTube.tube α β R,
        length F (OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
          (OriginalSecondHalfCompactTube.near α β R hR) z).2 <
            length F (α z.val.1) + length F (β z.val.2.2) + ε) ∧
      (∀ z : CompactNearJoinParameters.tube α β R,
        length F (CompactNearJoinParameters.inputs α β R hR z).val.1 +
          length F (CompactNearJoinParameters.inputs α β R hR z).val.2 <
            length F (α z.val.1) + length F (β z.val.2) + ε) := by
  obtain ⟨S, hS, hS1, hlength⟩ := OriginalSecondHalfCompactTube.exists_length_tube F α β hε
  let R₀ := min S (1 / 2)
  refine ⟨R₀, lt_min hS (by norm_num), min_le_right _ _, ?_⟩
  intro R hR hRR₀
  have hRS : R ≤ S := hRR₀.trans (min_le_left _ _)
  have htime : ∀ z : OriginalSecondHalfCompactTube.tube α β R,
      length F (OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) z).2 <
          length F (α z.val.1) + length F (β z.val.2.2) + ε := by
    intro z
    let zS : OriginalSecondHalfCompactTube.tube α β S := ⟨z.val, z.property.trans hRS⟩
    have he : (OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) z).2 =
      (OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β S)
        (OriginalSecondHalfCompactTube.near α β S hS1) zS).2 := rfl
    rw [he]
    exact hlength zS
  refine ⟨htime, ?_⟩
  intro z
  rw [FullSecondHalfCompactTimeOperation.corrected_length α β F R hR z]
  exact htime (CompactNearJoinParameters.timeMap α β R (0, z))

end
end Finsler.CompactJoinUniformTubeLength
