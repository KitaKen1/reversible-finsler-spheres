module

public import Finsler.Topology.EndgameFlow
public import Finsler.Topology.Shortening

/-! The final section with the level deformations and lenses replaced by two properties of
shortenings. `ShorteningInputs` keeps the other lemma-level inputs of `EndgameAssembly.Core`
and asks for a point of the sphere, positivity of the critical levels, the descent property
(on an interval without critical levels some shortening has an iterate taking the upper
sublevel into the lower one) and the localization property (at tight cuts around a critical
level some shortening D is such that the loops x with √E(D x) above the lower cut avoid the
point). These give the flow inputs, so they are contradictory as well. None of the inputs is
proved here. -/

@[expose] public section

namespace Finsler.EndgameShortening

open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.EndgameAssembly Finsler.EndgameFlow
open Set

noncomputable section

variable {n : ℕ}

/-- The lemma-level inputs of the final section for one reversible metric, with the vanishing
of e on single crossings replaced by the descent and localization properties of
shortenings. -/
structure ShorteningInputs (F : ReversibleMetric n) (hn : 1 ≤ n) extends Core F hn where
  /-- a point of the sphere avoided near the critical loops -/
  p : Sphere n
  crit_pos : ∀ c ∈ crit, 0 < c
  /-- descent on intervals without critical levels -/
  descent : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
    ∃ (S : Shortening.Data F b) (k : ℕ), ∀ x : lev F b, (x : Loops n) ∈ lev F a' →
      (Shortening.iter S k x : Loops n) ∈ lev F a
  /-- localization at tight cuts around each critical level -/
  localize : ∀ c ∈ crit, ∃ ε : ℝ, 0 < ε ∧
    ∀ a' b : ℝ, c - ε < a' → a' < c → c < b → b < c + ε →
      ∃ S : Shortening.Data F b, ∀ x : lev F b,
        a' < Real.sqrt (energy F (S.D x : SphereLoop n)) → (x : Loops n) ∈ AvoidPoint.avoid p

variable {F : ReversibleMetric n} {hn : 1 ≤ n}

/-- The flow inputs from the shortening inputs. -/
def toFlowInputs (I : ShorteningInputs F hn) : FlowInputs F hn where
  toCore := I.toCore
  p := I.p
  reg := (Shortening.flow_of_shortening F I.p I.crit I.crit_pos I.descent I.localize).1
  lens := (Shortening.flow_of_shortening F I.p I.crit I.crit_pos I.descent I.localize).2

/-- The shortening inputs of the final section are contradictory. -/
theorem false_of_shorteningInputs (h2 : 2 ≤ n) (I : ShorteningInputs F hn) : False :=
  false_of_flowInputs h2 (toFlowInputs I)

/-- If finiteness of the prime closed geodesic images yields the shortening inputs, there are
infinitely many prime closed geodesic images. -/
theorem infinite_of_shorteningInputs (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (h : (primeImages F).Finite → Nonempty (ShorteningInputs F (le_trans (by norm_num) h2))) :
    (primeImages F).Infinite := by
  intro hfin
  obtain ⟨I⟩ := h hfin
  exact false_of_shorteningInputs h2 I

/-- Reduction of the candidate main assertion to the shortening inputs. -/
theorem assertion_of_shorteningInputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (ShorteningInputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_shorteningInputs F (le_trans (by norm_num) h3) (h n h3 F)

end

end Finsler.EndgameShortening
