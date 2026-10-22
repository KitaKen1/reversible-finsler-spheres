module

public import Finsler.Analysis.H1LocalFiber

/-! Uniform additive length estimates in both directions of the genuine
strong-H¹ local product chart, after fixing the length bound. -/

@[expose] public section

namespace Finsler.LocalFiberLength

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1LocalFiber Finsler.H1FiberBase Finsler.SobolevLength
open Set

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem exists_chart_control (F : ReversibleMetric n) (M : ℝ) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ (y : Sphere n) (u : nearFiber y),
        dist (y : Ambient n) (basepoint u.val) < ρ → length F u.val ≤ M →
        |length F ((chart y u).2.val) - length F u.val| < ε) ∧
      (∀ (y : Sphere n) (p : nearBases y × based y),
        dist (p.1.val : Ambient n) (y : Ambient n) < ρ → length F p.2.val ≤ M →
        |length F ((chart y).symm p).val - length F p.2.val| < ε) := by
  obtain ⟨r, hr, hd⟩ := Finsler.H1BasepointAlignment.exists_alignment F M hM hε
  have hctrl (u : SphereLoop n) (y : Sphere n)
      (hy : dist (y : Ambient n) (basepoint u) < r) (hlen : length F u ≤ M) :
      |length F (align u y) - length F u| < ε := by
    exact (hd _ _ (u.sphere_constraint ⟨0, by norm_num⟩)
      (by simpa using y.property) hy u rfl hlen).2
  refine ⟨min 1 r, lt_min zero_lt_one hr, min_le_left 1 r, ?_, ?_⟩
  · intro y u hy hlen
    change |length F (align u.val y) - length F u.val| < ε
    exact hctrl u.val y (hy.trans_le (min_le_right 1 r)) hlen
  · intro y p hx hlen
    change |length F (align p.2.val p.1.val) - length F p.2.val| < ε
    apply hctrl p.2.val p.1.val ?_ hlen
    rw [p.2.property]
    exact hx.trans_le (min_le_right 1 r)


end
end Finsler.LocalFiberLength
