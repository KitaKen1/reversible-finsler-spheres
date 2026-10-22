module

public import Finsler.Topology.BorelCrossing
public import Finsler.Geometry.PrimeRepresentative

/-! The final step of the argument as a reduction with actual groups. `EndgameData` lists what
the geometric stages must construct from the assumption that only finitely many prime closed
geodesic images exist: an increasing sequence of cuts, a global reflection Borel class which is
zero at the first cut and nonzero at the last, vanishing of e on the crossing groups, and at
every successor cut a doubling rank budget on a plateau whose distinguished label has the bottom
indicator of the class and a partner indicator not exceeding that of its e-multiple. Such data
is contradictory, by the first-appearance argument for the actual reflection Borel cohomology
and the equality case of the doubling formula. Hence the main assertion follows once the data
is constructed for every metric with finitely many prime images. No such construction is made
in this file: detection, bounded defect, doubling and local vanishing remain open. -/

@[expose] public section

namespace Finsler.Endgame

open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelCrossing

noncomputable section

variable {n : ℕ}

/-- The inputs of the final contradiction, stated with the actual reflection Borel groups of the
Finsler sublevels. The partner indicator of the budget may be smaller than the indicator of a
nonzero e-multiple: in the doubling formula it counts independence modulo bottom images. -/
structure EndgameData (F : ReversibleMetric n) (hn : 1 ≤ n) where
  q : ℕ
  ξ : HR (fullComplex n) q
  m : ℕ
  c : ℕ → ℝ
  mono : Monotone c
  ι : Type
  budgets : ℕ → Finsler.PartnerRank.Data ι
  label : ℕ → ι
  zero_start : HRmap (resHom F (c 0)) q ξ = 0
  nonzero_end : HRmap (resHom F (c m)) q ξ ≠ 0
  local_zero : ∀ i, i < m → ∀ z, crossE F (mono (Nat.le_succ i)) hn q z = 0
  member : ∀ i, i < m → label i ∈ (budgets i).labels
  bottom_rank : ∀ i, i < m → (budgets i).bottom (label i) =
    Finsler.FirstAppearance.bottom (firstData F c mono hn q) ξ (i + 1)
  partner_le : ∀ i, i < m → (budgets i).partner (label i) ≤
    Finsler.FirstAppearance.partner (firstData F c mono hn q) ξ (i + 1)
  plateau : ∀ i, i < m → (budgets i).Tdouble = (budgets i).T

/-- Endgame data is contradictory: at the first cut where the class is visible its e-multiple
vanishes, while the plateau forces the partner indicator to equal the bottom indicator. -/
theorem endgame_contradiction {F : ReversibleMetric n} {hn : 1 ≤ n}
    (D : EndgameData F hn) : False := by
  obtain ⟨i, hi, hb, hp⟩ := Finsler.FirstAppearance.first_partner_gap
    (firstData F D.c D.mono hn D.q) D.ξ D.m D.zero_start D.nonzero_end D.local_zero
  have heq := Finsler.PartnerRank.equality_forces_partner (D.budgets i) (D.plateau i hi)
    (D.label i) (D.member i hi)
  have hle := D.partner_le i hi
  rw [heq, D.bottom_rank i hi, hb, hp] at hle
  norm_num at hle

/-- If finiteness of the prime closed geodesic images yields endgame data, there are infinitely
many prime closed geodesic images. -/
theorem infinite_of_endgame (F : ReversibleMetric n) (hn : 1 ≤ n)
    (h : (primeImages F).Finite → Nonempty (EndgameData F hn)) : (primeImages F).Infinite := by
  intro hfin
  obtain ⟨D⟩ := h hfin
  exact endgame_contradiction D

/-- Reduction of the main assertion to the construction of endgame data for every reversible
metric with finitely many prime closed geodesic images on a sphere of dimension at least
three. -/
theorem assertion_of_endgame
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (EndgameData F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_endgame F (le_trans (by norm_num) h3) (h n h3 F)

end

end Finsler.Endgame
