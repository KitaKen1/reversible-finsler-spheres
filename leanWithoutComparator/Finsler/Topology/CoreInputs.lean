module

public import Finsler.Topology.DefectBound
public import Finsler.Topology.BasisBudget

/-! The inputs which remain for the main assertion. `CoreInputs` collects, for one reversible
metric with finitely many prime closed geodesic images, a global basis with its K-lifts
(`BasisBudget.Data`), the local bounds for single crossings (`EventSum.EventBounds`), the gap
structure at large cuts (`DefectBound.GapInputs`) and the detection band. The bound for the
defect follows from the second and third (`DefectBound.exists_defect_le`), so these inputs give
`BasisBudget.BasisInputs`, hence the level inputs of the final section, and they are
contradictory. The candidate main assertion follows if they exist for every metric with finitely
many prime closed geodesic images. The local event input is now constructed by
`ActualWindowPieces.nonempty_eventBounds`; `CoreGlobal` retains only the global inputs.
This legacy interface and its theorem types remain unchanged. -/

@[expose] public section

namespace Finsler.CoreInputs

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.EventSum Finsler.DefectBound Finsler.BasisBudget
open Finsler.EndgameAssembly Finsler.EndgameLevels

noncomputable section

variable {n : ℕ}

/-- The inputs which remain: a global basis, local bounds for single crossings, the gap
structure at large cuts, and the detection band. -/
structure Inputs (F : ReversibleMetric n) (hn : 1 ≤ n) where
  basis : Data n hn
  events : EventBounds F
  gaps : GapInputs F
  /-- detection band -/
  α : ℝ
  α_pos : 0 < α
  C : ℝ
  q₀ : ℕ
  det_inj : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → (q : ℝ) < α * a - C →
    Function.Injective (HRmap (resHom F a) q)
  det_zero : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → α * a + C < (q : ℝ) →
    ∀ x, HRmap (resHom F a) q x = 0

variable {F : ReversibleMetric n} {hn : 1 ≤ n}

/-- With finitely many prime closed geodesic images, the remaining inputs give a global basis, a
bound for the defect and a detection band. -/
theorem nonempty_basisInputs (hfin : (primeImages F).Finite) (I : Inputs F hn) :
    Nonempty (BasisInputs F hn) := by
  obtain ⟨B, hB⟩ := exists_defect_le I.events I.gaps hn hfin
  exact ⟨{ basis := I.basis
           bound := B
           defect_le := hB
           α := I.α
           α_pos := I.α_pos
           C := I.C
           q₀ := I.q₀
           det_inj := I.det_inj
           det_zero := I.det_zero }⟩

/-- With finitely many prime closed geodesic images, the remaining inputs are contradictory. -/
theorem false_of_inputs (h2 : 2 ≤ n) (hfin : (primeImages F).Finite) (I : Inputs F hn) :
    False := by
  obtain ⟨J⟩ := nonempty_basisInputs hfin I
  exact false_of_basisInputs h2 hfin J

/-- Reduction of the candidate main assertion to the remaining inputs for every metric with
finitely many prime closed geodesic images. -/
theorem assertion_of_inputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (Inputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  assertion_of_basisInputs fun n h3 F hfin => by
    obtain ⟨I⟩ := h n h3 F hfin
    exact nonempty_basisInputs hfin I

end

end Finsler.CoreInputs
