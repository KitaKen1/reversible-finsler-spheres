module

public import Finsler.Loop.SingleInputCutMetricAdequacy
public import Finsler.Loop.CompactFactorCoverRefinement
public import Finsler.Loop.FirstInputSelfCutCover

/-! Real compact-family cut geometry at arbitrary native-compatible
support radii, chosen before all cochains, degrees and length bounds. -/

@[expose] public section
namespace Finsler.SingleInputUniformCanonicalGeometry
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem exists_scale {P : Type} [PseudoMetricSpace P] [CompactSpace P] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) {κ ρ ε b : ℝ}
    (hκ : 0 < κ) (hρr : ρ < r) (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (hb : 0 < b) :
    ∃ σ > 0, σ ≤ b ∧
      ∃ index : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r),
      (∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ FirstInputSelfCutCover.cover α r hr κ ρ (index c)) ∧
      SingleInputCutMetricAdequacy.Adequate α r hr F ε σ := by
  obtain ⟨σ₀, hσ₀, hσ₀b, hscale⟩ := SingleInputCutMetricAdequacy.exists_scale α r hr F hε hb
  obtain ⟨σ, hσ, hσσ₀, index, hindex⟩ := CompactFactorCoverRefinement.exists_factor
    (FirstInputSelfCutCover.cover α r hr κ ρ) (FirstInputSelfCutCover.cover_open α r hr κ ρ)
    (FirstInputSelfCutCover.cover_univ α r hr κ hκ hρr) hσ₀
  exact ⟨σ, hσ, hσσ₀.trans hσ₀b, index, hindex, hscale σ hσσ₀⟩

end
end Finsler.SingleInputUniformCanonicalGeometry
