module

public import Finsler.Topology.CoreInputs
public import Finsler.Topology.ActualWindowPieces

/-! The local event input is constructed from the actual metric. The remaining interface
contains the global basis, global gap/filling/resonance data and detection band. -/

@[expose] public section

namespace Finsler.CoreGlobal

open Set Module Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.DefectBound Finsler.BasisBudget

noncomputable section

variable {n : ℕ}

structure Inputs (F : ReversibleMetric n) (hn : 1 ≤ n) where
  basis : Data n hn
  gaps : GapInputs F
  α : ℝ
  α_pos : 0 < α
  C : ℝ
  q₀ : ℕ
  det_inj : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → (q : ℝ) < α * a - C →
    Function.Injective (HRmap (resHom F a) q)
  det_zero : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → α * a + C < (q : ℝ) →
    ∀ x, HRmap (resHom F a) q x = 0

theorem nonempty_coreInputs {F : ReversibleMetric n} {hn : 1 ≤ n}
    (hfin : (primeImages F).Finite) (I : Inputs F hn) : Nonempty (Finsler.CoreInputs.Inputs F hn) := by
  obtain ⟨E⟩ := Finsler.ActualWindowPieces.nonempty_eventBounds F hn hfin
  exact ⟨⟨I.basis, E, I.gaps, I.α, I.α_pos, I.C, I.q₀, I.det_inj, I.det_zero⟩⟩

theorem false_of_inputs {F : ReversibleMetric n} {hn : 1 ≤ n} (h2 : 2 ≤ n)
    (hfin : (primeImages F).Finite) (I : Inputs F hn) : False := by
  obtain ⟨J⟩ := nonempty_coreInputs hfin I
  exact Finsler.CoreInputs.false_of_inputs h2 hfin J

theorem assertion_of_inputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (Inputs F (le_trans (by norm_num) h3))) : ReversibleSphereAssertion :=
  Finsler.CoreInputs.assertion_of_inputs fun n h3 F hfin => by
    obtain ⟨I⟩ := h n h3 F hfin
    exact nonempty_coreInputs hfin I

end

end Finsler.CoreGlobal
