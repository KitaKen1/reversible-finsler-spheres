module

public import Finsler.Topology.EndgameDefect
public import Finsler.Geometry.CriticalLevels

/-! The final section with the concrete critical levels. `LevelInputs` keeps the lemma-level
inputs of `EndgameDefect.DefectInputs` that are statements about Borel cohomology (boundedness
of the defect, the doubling rank budgets, the detection band, the odd bottom classes) and states
them for the set `CriticalLevels.crit` of numbers 2^m √E(u), u a tangent critical loop of
positive energy. With finitely many prime closed geodesic images this set is locally finite,
closed under doubling, positive and contains √E of every tangent critical loop of positive
energy, so the level inputs give the defect inputs and are contradictory. The level inputs
themselves are not proved here. -/

@[expose] public section

namespace Finsler.EndgameLevels

open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.BorelCochain Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCurveVariation Finsler.EndgameAssembly Finsler.EndgameDefect
open Finsler.CriticalLevels
open Set

noncomputable section

variable {n : ℕ}

/-- The lemma-level inputs of the final section for one reversible metric, for the concrete set
of critical levels and with the defect of a cut as T. -/
structure LevelInputs (F : ReversibleMetric n) (hn : 1 ≤ n) where
  /-- boundedness of the defect -/
  bound : ℕ
  defect_le : ∀ a, 0 < a → a ∉ crit F → Defect.defect F a ≤ bound
  /-- labels of the doubling formula -/
  ι : Type
  budget : ℝ → Finsler.PartnerRank.Data ι
  budget_T : ∀ x, 0 < x → x ∉ crit F → (budget x).T = (Defect.defect F (x / 2) : ℤ)
  budget_Tdouble : ∀ x, 0 < x → x ∉ crit F → (budget x).Tdouble = (Defect.defect F x : ℤ)
  /-- detection band -/
  α : ℝ
  α_pos : 0 < α
  C : ℝ
  q₀ : ℕ
  det_inj : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → (q : ℝ) < α * a - C →
    Function.Injective (HRmap (resHom F a) q)
  det_zero : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → α * a + C < (q : ℝ) →
    ∀ x, HRmap (resHom F a) q x = 0
  /-- odd bottom classes -/
  bottom : ∀ t : ℕ, HR (fullComplex n) ((4 * t + 1) * (n - 1))
  bottom_ne : ∀ t, bottom t ≠ 0
  label : ℕ → ι
  label_mem : ∀ t x, 0 < x → x ∉ crit F → HRmap (resHom F x) _ (bottom t) ≠ 0 →
    label t ∈ (budget x).labels
  label_bottom : ∀ t x, 0 < x → x ∉ crit F → HRmap (resHom F x) _ (bottom t) ≠ 0 →
    (budget x).bottom (label t) = 1
  label_partner : ∀ t x, 0 < x → x ∉ crit F →
    BorelCanonicalEvaluation.levE F x hn _ (HRmap (resHom F x) _ (bottom t)) = 0 →
    (budget x).partner (label t) ≤ 0

variable {F : ReversibleMetric n} {hn : 1 ≤ n}

/-- The defect inputs from the level inputs, for finitely many prime closed geodesic images. -/
def toDefectInputs (hfin : (primeImages F).Finite) (I : LevelInputs F hn) :
    DefectInputs F hn where
  crit := crit F
  crit_finite := crit_finite F hfin
  crit_double := fun _ hx => crit_double F hx
  crit_pos := fun _ hc => crit_pos F hc
  crit_mem := crit_mem F
  bound := I.bound
  defect_le := I.defect_le
  ι := I.ι
  budget := I.budget
  budget_T := I.budget_T
  budget_Tdouble := I.budget_Tdouble
  α := I.α
  α_pos := I.α_pos
  C := I.C
  q₀ := I.q₀
  det_inj := I.det_inj
  det_zero := I.det_zero
  bottom := I.bottom
  bottom_ne := I.bottom_ne
  label := I.label
  label_mem := I.label_mem
  label_bottom := I.label_bottom
  label_partner := I.label_partner

/-- With finitely many prime closed geodesic images, the level inputs are contradictory. -/
theorem false_of_levelInputs (h2 : 2 ≤ n) (hfin : (primeImages F).Finite)
    (I : LevelInputs F hn) : False :=
  false_of_defectInputs h2 hfin (toDefectInputs hfin I)

/-- If finiteness of the prime closed geodesic images yields the level inputs, there are
infinitely many prime closed geodesic images. -/
theorem infinite_of_levelInputs (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (h : (primeImages F).Finite → Nonempty (LevelInputs F (le_trans (by norm_num) h2))) :
    (primeImages F).Infinite := by
  intro hfin
  obtain ⟨I⟩ := h hfin
  exact false_of_levelInputs h2 hfin I

/-- Reduction of the candidate main assertion to the level inputs. -/
theorem assertion_of_levelInputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (LevelInputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_levelInputs F (le_trans (by norm_num) h3) (h n h3 F)

end

end Finsler.EndgameLevels
