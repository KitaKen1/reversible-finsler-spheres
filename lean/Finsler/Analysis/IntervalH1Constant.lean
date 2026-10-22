module

public import Finsler.Analysis.IntervalH1
public import Finsler.Analysis.IntervalWeakConstant

/-! The zero-velocity kernel of the actual interval H¹ weak-derivative graph.
The conclusion is a.e. constancy of its genuine L² value, not an assumed
continuous representative or an arbitrary supplied velocity field. -/

@[expose] public section

namespace Finsler.IntervalSobolev

open Finsler.SphereGeometry MeasureTheory Filter
open scoped Topology

noncomputable section

theorem exists_ae_const_of_velocity_eq_zero {n : ℕ} (u : Space n)
    (hzero : velocity u = 0) :
    ∃ c : Ambient n, value u =ᵐ[intervalMeasure] fun _ => c := by
  have hh := (TauCeti.hasWeakFDerivOn_iff.mp (value_hasWeakFDeriv u)) (1 : ℝ)
  have hz : (fun t => derivative u t 1) =ᵐ[intervalMeasure] fun _ => (0 : Ambient n) := by
    have hv := velocity_apply_ae u
    rw [hzero] at hv
    exact hv.symm.trans (Lp.coeFn_zero _ _ _)
  have hweak := hh.congr_ae_deriv hz
  exact Finsler.IntervalWeakConstant.exists_ae_const_of_weak_line_zero hweak

end

end Finsler.IntervalSobolev
