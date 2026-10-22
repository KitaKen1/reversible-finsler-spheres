module

public import Finsler.Loop.CompactJoinUniformTubeLength

/-! Actual original closed-tube joined families have one uniform
length margin before all later individual input bounds. -/

@[expose] public section
namespace Finsler.CompactJoinedFamilyUniformLength
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevLength Finsler.JoinedComparisonAdequacy
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {n : ℕ}
    (F : ReversibleMetric n) (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R ≤ u →
      ∀ (A : ℝ), (∀ x y, length F (α x) + length F (β y) < A) →
      ∀ z : CompactNearJoinParameters.tube α β R,
        length F (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) z) < A + ε := by
  obtain ⟨u, hu, hu1, hscale⟩ := CompactJoinUniformTubeLength.exists_uniform F α β hε
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu A hA z
  have hl := (hscale R (hR.trans_lt (by norm_num)) hRu).2 z
  have hj := JoinedComparisonAdequacy.family_length F
    (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) 0 (by norm_num) (by norm_num) 0
    ⟨((0, 0), z), Set.mem_univ _⟩
  change length F (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) z) = _ at hj
  rw [hj]
  exact hl.trans (by linarith [hA z.val.1 z.val.2])

end
end Finsler.CompactJoinedFamilyUniformLength
