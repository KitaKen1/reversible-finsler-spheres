module

public import Finsler.Geometry.RoundLoopCross
public import Finsler.Geometry.RoundV2Dims
public import Finsler.Topology.PatternOfNil
public import Finsler.Geometry.RoundCrossW
public import Finsler.Topology.BorelGraded

/-! The Gysin pattern of a round crossing.

For n ≥ 2 and cuts 2π(m − 1) < a < 2πm < b < 2π(m + 1), the ordinary cohomology of the round
crossing pair is that of V₂ shifted by l = (2m − 1)(n − 1): finite dimensional, of dimension at
most one in every degree, supported in the degrees l, l + d, l + d + 1 and l + 2d + 1 (d = n − 1),
and nonzero in degree l. With w^{n+1} = 0 on the crossing (`RoundCrossW`), the reflection Borel
cohomology of the crossing is the Gysin pattern of two w-towers as soon as the e-multiple of the
start class τ is not forgotten to zero (the e-compatibility, the remaining input). -/

@[expose] public section

namespace Finsler.RoundCrossPattern

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundThom Finsler.RoundLoopCross Finsler.RoundV2Dims Finsler.TrivHq
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelCrossing Finsler.CriticalLevels Finsler.GysinPattern Finsler.PatternOfNil
open Finsler.NilpotentW Finsler.BorelGraded
open Set Module
open scoped Real

noncomputable section

variable {n : ℕ} (hn : 2 ≤ n) {m : ℕ} (hm : 0 < m) {a b : ℝ}
  (hlo : 2 * π * ((m : ℝ) - 1) < a) (hac : a < 2 * π * m) (hcb : 2 * π * m < b)
  (hhi : b < 2 * π * ((m : ℝ) + 1)) (hab : a ≤ b)

/-- The index of the crossing. -/
abbrev lc (n m : ℕ) : ℕ := (2 * m - 1) * (n - 1)

include hn hm hlo hac hcb hhi in
theorem cross_fin (q : ℕ) :
    FiniteDimensional (ZMod 2) (H (crossComplex (roundMetric n) hab) q) :=
  (round_cross_dims (by omega) hm hlo hac hcb hhi hab q).1

include hn hm hlo hac hcb hhi in
theorem cross_finrank (q : ℕ) :
    finrank (ZMod 2) (H (crossComplex (roundMetric n) hab) q) =
      if lc n m ≤ q then finrank (ZMod 2) (HV n (q - lc n m)) else 0 :=
  (round_cross_dims (by omega) hm hlo hac hcb hhi hab q).2

include hn hm hlo hac hcb hhi in
theorem cross_dim (q : ℕ) : finrank (ZMod 2) (H (crossComplex (roundMetric n) hab) q) ≤ 1 := by
  rw [cross_finrank hn hm hlo hac hcb hhi hab q]
  split_ifs
  · exact V2_finrank_le_one hn _
  · exact zero_le_one

include hn hm hlo hac hcb hhi in
theorem cross_zero_of_finrank {q : ℕ}
    (h : finrank (ZMod 2) (H (crossComplex (roundMetric n) hab) q) = 0)
    (z : H (crossComplex (roundMetric n) hab) q) : z = 0 := by
  haveI := cross_fin hn hm hlo hac hcb hhi hab q
  have := Module.finrank_zero_iff.mp h
  exact Subsingleton.elim _ _

include hn hm hlo hac hcb hhi in
theorem cross_supp (q : ℕ) (h1 : q ≠ lc n m) (h2 : q ≠ lc n m + (n - 1))
    (h3 : q ≠ lc n m + (n - 1) + 1) (h4 : q ≠ lc n m + (n - 1) + 1 + (n - 1))
    (z : H (crossComplex (roundMetric n) hab) q) : z = 0 := by
  refine cross_zero_of_finrank hn hm hlo hac hcb hhi hab ?_ z
  rw [cross_finrank hn hm hlo hac hcb hhi hab q]
  split_ifs with h
  · have hz : ∀ x : HV n (q - lc n m), x = 0 :=
      V2_eq_zero hn (q - lc n m) (by omega) (by omega) (by omega) (by omega)
    haveI : Subsingleton (HV n (q - lc n m)) := ⟨fun x y => (hz x).trans (hz y).symm⟩
    exact Module.finrank_zero_of_subsingleton
  · rfl

include hn hm hlo hac hcb hhi in
theorem cross_below (q : ℕ) (hq : q < lc n m) (z : H (crossComplex (roundMetric n) hab) q) :
    z = 0 := by
  refine cross_zero_of_finrank hn hm hlo hac hcb hhi hab ?_ z
  rw [cross_finrank hn hm hlo hac hcb hhi hab q, if_neg (by omega)]

include hn hm hlo hac hcb hhi in
theorem cross_bottom : ∃ z : H (crossComplex (roundMetric n) hab) (lc n m), z ≠ 0 := by
  haveI := cross_fin hn hm hlo hac hcb hhi hab (lc n m)
  have h := cross_finrank hn hm hlo hac hcb hhi hab (lc n m)
  rw [if_pos le_rfl, Nat.sub_self] at h
  have hpos : 0 < finrank (ZMod 2) (H (crossComplex (roundMetric n) hab) (lc n m)) := by
    rw [h]
    exact V2_H0_pos hn
  exact Module.finrank_pos_iff_exists_ne_zero.mp hpos

include hn hm hlo hac hcb hhi in
/-- The start class of the crossing. -/
theorem cross_start : ∃ τ : HR (crossComplex (roundMetric n) hab) (lc n m),
    forget _ (lc n m) τ ≠ 0 :=
  exists_start (cross_below hn hm hlo hac hcb hhi hab) (cross_bottom hn hm hlo hac hcb hhi hab)

/-! ### The cuts are regular and enclose one critical level -/

include hm hlo hac in
theorem a_not_crit : a ∉ crit (roundMetric n) := by
  intro h
  obtain ⟨m', hm', rfl⟩ := Finsler.RoundCrossW.crit_round h
  have hπ := Real.pi_pos
  have h1 : (m : ℝ) - 1 < m' := lt_of_mul_lt_mul_left hlo (by positivity)
  have h2 : (m' : ℝ) < m := lt_of_mul_lt_mul_left hac (by positivity)
  have e1 : m < m' + 1 := by exact_mod_cast (show (m : ℝ) < m' + 1 by linarith)
  have e2 : m' < m := by exact_mod_cast h2
  omega

include hcb hhi in
theorem b_not_crit : b ∉ crit (roundMetric n) := by
  intro h
  obtain ⟨m', hm', rfl⟩ := Finsler.RoundCrossW.crit_round h
  have hπ := Real.pi_pos
  have h1 : (m : ℝ) < m' := lt_of_mul_lt_mul_left hcb (by positivity)
  have h2 : (m' : ℝ) < m + 1 := lt_of_mul_lt_mul_left hhi (by positivity)
  have e1 : m < m' := by exact_mod_cast h1
  have e2 : m' < m + 1 := by exact_mod_cast h2
  omega

include hlo hhi in
theorem crit_subsingleton : (crit (roundMetric n) ∩ Icc a b).Subsingleton := by
  have hπ := Real.pi_pos
  have key : ∀ c ∈ crit (roundMetric n) ∩ Icc a b, c = 2 * π * m := by
    rintro c ⟨hc, hca, hcb'⟩
    obtain ⟨m', hm', rfl⟩ := Finsler.RoundCrossW.crit_round hc
    have h1 : (m : ℝ) - 1 < m' := lt_of_mul_lt_mul_left (hlo.trans_le hca) (by positivity)
    have h2 : (m' : ℝ) < m + 1 := lt_of_mul_lt_mul_left (hcb'.trans_lt hhi) (by positivity)
    have e1 : m < m' + 1 := by exact_mod_cast (show (m : ℝ) < m' + 1 by linarith)
    have e2 : m' < m + 1 := by exact_mod_cast h2
    have : m' = m := by omega
    rw [this]
  intro c hc c' hc'
  rw [key c hc, key c' hc']

include hn hm hlo hac hcb hhi in
theorem cross_w (q : ℕ) (z : HR (crossComplex (roundMetric n) hab) q) :
    wPow (crossComplex (roundMetric n) hab) q (n + 1) z = 0 := by
  have hπ := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 < a := lt_of_le_of_lt (by nlinarith) hlo
  exact Finsler.RoundCrossW.crossW_pow_zero (by omega) hab ha (a_not_crit hm hlo hac)
    (b_not_crit hcb hhi) (crit_subsingleton hlo hhi) q z

/-! ### The pattern -/

theorem deg_eq (hn : 2 ≤ n) (l : ℕ) : n + l = l + (n - 1) + 1 := by omega

include hn hm hlo hac hcb hhi in
/-- **The Gysin pattern of a round crossing**, given the e-compatibility of its start class. -/
def roundPattern (τ : HR (crossComplex (roundMetric n) hab) (lc n m))
    (hτ : forget _ (lc n m) τ ≠ 0)
    (he : forget _ (lc n m + (n - 1) + 1)
      (castHR (deg_eq hn (lc n m)) (crossE (roundMetric n) hab (by omega) (lc n m) τ)) ≠ 0) :
    Pattern (crossComplex (roundMetric n) hab) (lc n m) (n - 1) :=
  patternOfNil (k := n + 1) (by omega) (cross_fin hn hm hlo hac hcb hhi hab)
    (cross_dim hn hm hlo hac hcb hhi hab) (cross_supp hn hm hlo hac hcb hhi hab) τ hτ
    (castHR (deg_eq hn (lc n m)) (crossE (roundMetric n) hab (by omega) (lc n m) τ)) he
    (cross_w hn hm hlo hac hcb hhi hab)

end

end Finsler.RoundCrossPattern
