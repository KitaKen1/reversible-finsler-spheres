module

public import Finsler.Analysis.H1OrthogonalContinuity
public import Finsler.Topology.SupportedSelfCut

/-! Orthogonal rotation preserves the actual round self-cut distance
of a strong H1 loop, including both time endpoints. -/

@[expose] public section
namespace Finsler.OrthogonalSelfCutDistance

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1OrthogonalLength Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

theorem distance {n : ℕ} (A : Ambient n ≃ₗᵢ[ℝ] Ambient n)
    (γ : SphereLoop n) (t : ClosedInterval) :
    SupportedSelfCut.distance n (t, rotateLoop A γ) = SupportedSelfCut.distance n (t, γ) := by
  change ‖continuousRepresentative (rotateData A (γ.data : Space n)) t -
    continuousRepresentative (rotateData A (γ.data : Space n)) 0‖ = _
  rw [representative_rotateData A _ t.property, representative_rotateData A _ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1),
    ← A.map_sub, A.norm_map]
  rfl

end
end Finsler.OrthogonalSelfCutDistance
