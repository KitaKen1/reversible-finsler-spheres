module

public import Finsler.Analysis.H1BasepointAlignment
public import Finsler.Analysis.H1OrthogonalContinuity

/-! Joint strong-H¹ continuity of the concrete basepoint correction. -/

@[expose] public section

namespace Finsler.H1AlignmentContinuity

open Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.NearbyRotor Finsler.H1OrthogonalLength Finsler.H1OrthogonalContinuity
open scoped Topology

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def correctionDomain (n : ℕ) : Set (Ambient n × Ambient n) :=
  {p | p.1 ≠ 0 ∧ p.1 + p.2 ≠ 0}

theorem continuous_operator : Continuous (fun p : correctionDomain n =>
    (rotor p.val.1 p.val.2).toContinuousLinearMap) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have h := (rotor_continuousAt p.property.1 p.property.2).comp
    (f := fun q : correctionDomain n => q.val) (x := p)
    continuous_subtype_val.continuousAt
  exact h.congr (Filter.Eventually.of_forall fun q => rfl)

/-- The loop and both correction points can vary together in an external family. -/
theorem continuous_correction : Continuous (fun z : correctionDomain n × SphereLoop n =>
    rotateLoop (rotor z.1.val.1 z.1.val.2) z.2) := by
  have hA : Continuous (fun z : correctionDomain n × SphereLoop n =>
      (rotor z.1.val.1 z.1.val.2).toContinuousLinearMap) :=
    (continuous_operator.comp continuous_fst).congr (fun z => rfl)
  exact continuous_rotateLoop_family (n := n)
    (fun z : correctionDomain n × SphereLoop n => rotor z.1.val.1 z.1.val.2)
    hA Prod.snd continuous_snd


end
end Finsler.H1AlignmentContinuity
