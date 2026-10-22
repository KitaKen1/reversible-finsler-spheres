module

public import Finsler.Topology.EndgameCritical
public import Finsler.Topology.Defect

/-! The final section with the concrete defect. `DefectInputs` lists the lemma-level inputs of
the final section with T(a) taken to be the defect of the cut a (the sum over all degrees of
the dimensions of the cokernels of the restriction of global reflection Borel classes) and with
the critical levels required to be positive and to contain √E of every tangent critical loop of
positive energy. Two inputs of `EndgameAssembly.Inputs` are then theorems: the vanishing of e
on single crossings (v0.82) and the constancy of T between critical levels, which follows from
the descent of the curve shortening map on intervals without critical loops. With finitely
many prime closed geodesic images the defect inputs are contradictory. The inputs themselves
(local finiteness of critical levels and closure under doubling, boundedness of the defect,
doubling rank budgets, the detection band, the odd bottom classes) are not proved here. -/

@[expose] public section

namespace Finsler.EndgameDefect

open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.BorelCochain Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCurveVariation Finsler.EndgameAssembly Finsler.EndgameCritical
open Set

noncomputable section

variable {n : ℕ}

/-- The defect is the same at two cuts with no tangent critical loop of energy between
them. -/
theorem defect_eq_of_regular (F : ReversibleMetric n) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b)
    (hreg : ∀ u : SphereLoop n, TangentCritical F u → a ^ 2 ≤ energy F u →
      energy F u ≤ b ^ 2 → False) :
    Defect.defect F a = Defect.defect F b := by
  obtain ⟨S, k, hk⟩ := BirkhoffDescent.exists_descent F hn ha hab le_rfl hreg
  exact Defect.defect_eq_of_levelDeformation F hab (Shortening.levelDeformation S k hk)

/-- The lemma-level inputs of the final section for one reversible metric, with the defect of
a cut as T. -/
structure DefectInputs (F : ReversibleMetric n) (hn : 1 ≤ n) where
  /-- critical levels -/
  crit : Set ℝ
  crit_finite : ∀ a b : ℝ, (crit ∩ Icc a b).Finite
  crit_double : ∀ x, x ∈ crit → 2 * x ∈ crit
  crit_pos : ∀ c ∈ crit, 0 < c
  crit_mem : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u →
    Real.sqrt (energy F u) ∈ crit
  /-- boundedness of the defect -/
  bound : ℕ
  defect_le : ∀ a, 0 < a → a ∉ crit → Defect.defect F a ≤ bound
  /-- labels of the doubling formula -/
  ι : Type
  budget : ℝ → Finsler.PartnerRank.Data ι
  budget_T : ∀ x, 0 < x → x ∉ crit → (budget x).T = (Defect.defect F (x / 2) : ℤ)
  budget_Tdouble : ∀ x, 0 < x → x ∉ crit → (budget x).Tdouble = (Defect.defect F x : ℤ)
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
  label_mem : ∀ t x, 0 < x → x ∉ crit → HRmap (resHom F x) _ (bottom t) ≠ 0 →
    label t ∈ (budget x).labels
  label_bottom : ∀ t x, 0 < x → x ∉ crit → HRmap (resHom F x) _ (bottom t) ≠ 0 →
    (budget x).bottom (label t) = 1
  label_partner : ∀ t x, 0 < x → x ∉ crit →
    BorelCanonicalEvaluation.levE F x hn _ (HRmap (resHom F x) _ (bottom t)) = 0 →
    (budget x).partner (label t) ≤ 0

variable {F : ReversibleMetric n} {hn : 1 ≤ n}

/-- The core inputs from the defect inputs: the defect is constant between critical levels. -/
def toCore (I : DefectInputs F hn) : Core F hn where
  crit := I.crit
  crit_finite := I.crit_finite
  crit_double := I.crit_double
  T := Defect.defect F
  bound := I.bound
  T_le := I.defect_le
  T_const := fun _ _ ha hab hreg =>
    defect_eq_of_regular F hn ha hab fun u hu h1 h2 =>
      hreg (Real.sqrt (energy F u))
        ⟨(Real.le_sqrt' ha).mpr h1, Real.sqrt_le_iff.mpr ⟨(ha.trans_le hab).le, h2⟩⟩
        (I.crit_mem u hu (lt_of_lt_of_le (pow_pos ha 2) h1))
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

/-- With finitely many prime closed geodesic images, the defect inputs are contradictory. -/
theorem false_of_defectInputs (h2 : 2 ≤ n) (hfin : (primeImages F).Finite)
    (I : DefectInputs F hn) : False :=
  false_of_core h2 hfin (toCore I) I.crit_pos I.crit_mem

/-- If finiteness of the prime closed geodesic images yields the defect inputs, there are
infinitely many prime closed geodesic images. -/
theorem infinite_of_defectInputs (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (h : (primeImages F).Finite → Nonempty (DefectInputs F (le_trans (by norm_num) h2))) :
    (primeImages F).Infinite := by
  intro hfin
  obtain ⟨I⟩ := h hfin
  exact false_of_defectInputs h2 hfin I

/-- Reduction of the candidate main assertion to the defect inputs. -/
theorem assertion_of_defectInputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (DefectInputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_defectInputs F (le_trans (by norm_num) h3) (h n h3 F)

end

end Finsler.EndgameDefect
