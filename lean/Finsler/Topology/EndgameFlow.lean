module

public import Finsler.Topology.EndgameAssembly
public import Finsler.Topology.RegularInterval

/-! The final section with the vanishing of e on single crossings replaced by its two geometric
sources. `FlowInputs` keeps the other lemma-level inputs of `EndgameAssembly.Inputs` and asks,
instead of the vanishing of e, for a point of the sphere, level deformations on intervals
without critical levels, and lenses for that point at tight cuts around each critical level.
These give the vanishing of e between regular cuts enclosing at most one critical level, so the
flow inputs are contradictory as well. None of the inputs is proved here. -/

@[expose] public section

namespace Finsler.EndgameFlow

open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.EndgameAssembly Finsler.RegularInterval Finsler.BorelLens
open Set

noncomputable section

variable {n : ℕ}

/-- The lemma-level inputs of the final section for one reversible metric, with the vanishing
of e on single crossings replaced by level deformations and lenses. -/
structure FlowInputs (F : ReversibleMetric n) (hn : 1 ≤ n) extends Core F hn where
  /-- a point of the sphere avoided by the loops of the lenses -/
  p : Sphere n
  /-- level deformations on intervals without critical levels -/
  reg : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
    Nonempty (LevelDeformation F a a' b)
  /-- lenses for tight cuts around each critical level -/
  lens : ∀ c ∈ crit, ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε →
    Nonempty (Lens F a b p)

variable {F : ReversibleMetric n} {hn : 1 ≤ n}

/-- The inputs of the final section from the flow inputs. -/
def toInputs (I : FlowInputs F hn) : Inputs F hn where
  toCore := I.toCore
  e_zero _ _ hab ha hac hbc hsub q z :=
    crossE_zero_of_flow F hn I.p I.crit I.reg I.lens hab ha hac hbc hsub q z

/-- The flow inputs of the final section are contradictory. -/
theorem false_of_flowInputs (h2 : 2 ≤ n) (I : FlowInputs F hn) : False :=
  false_of_inputs h2 (toInputs I)

/-- If finiteness of the prime closed geodesic images yields the flow inputs, there are
infinitely many prime closed geodesic images. -/
theorem infinite_of_flowInputs (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (h : (primeImages F).Finite → Nonempty (FlowInputs F (le_trans (by norm_num) h2))) :
    (primeImages F).Infinite := by
  intro hfin
  obtain ⟨I⟩ := h hfin
  exact false_of_flowInputs h2 I

/-- Reduction of the candidate main assertion to the flow inputs. -/
theorem assertion_of_flowInputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (FlowInputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_flowInputs F (le_trans (by norm_num) h3) (h n h3 F)

end

end Finsler.EndgameFlow
