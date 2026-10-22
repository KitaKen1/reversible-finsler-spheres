module

public import Finsler.Analysis.IntervalH1SpherePath
public import Mathlib.Analysis.Normed.Operator.Banach

/-! A closed-graph shortcut for the original Sobolev graph topology.
For a linear map from a Banach space, continuity of every actual trace
already implies strong H¹ continuity. No weak-velocity continuity is assumed. -/

@[expose] public section

namespace Finsler.H1TraceClosedGraph

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Set

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem continuous_of_traces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (L : E →ₗ[ℝ] Space n)
    (h : ∀ t : ClosedInterval, Continuous (fun x => traceL n t (L x))) : Continuous L := by
  apply L.continuous_of_isClosed_graph
  have he : (L.graph : Set (E × Space n)) =
      {p | ∀ t : ClosedInterval, traceL n t p.2 = traceL n t (L p.1)} := by
    ext p
    constructor
    · intro hp t
      exact congrArg (traceL n t) ((L.mem_graph_iff p).mp hp)
    · intro hp
      apply (L.mem_graph_iff p).mpr
      apply eq_of_representative_eqOn
      intro τ hτ
      exact hp ⟨τ, hτ⟩
  have hi : {p : E × Space n | ∀ t : ClosedInterval,
      traceL n t p.2 = traceL n t (L p.1)} =
      ⋂ t : ClosedInterval, {p : E × Space n | traceL n t p.2 = traceL n t (L p.1)} := by
    ext p
    simp
  rw [he, hi]
  exact isClosed_iInter fun t => isClosed_eq
    ((traceL n t).continuous.comp continuous_snd) ((h t).comp continuous_fst)


end
end Finsler.H1TraceClosedGraph
