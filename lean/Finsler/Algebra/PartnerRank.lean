module

public import Finsler.Algebra.Budget

/-! The doubling rank formula with its finite family of actual partner ranks.
This packages explicit numerical hypotheses; constructing those ranks from
Finsler equivariant cohomology is a separate obligation. -/

@[expose] public section

namespace Finsler.PartnerRank

/-- The finite-cut numerical data used by the doubling argument. -/
structure Data (ι : Type*) where
  labels : Finset ι
  bottom : ι → ℤ
  partner : ι → ℤ
  T : ℤ
  Tdouble : ℤ
  J : ℤ
  Ve : ℤ
  V : ℤ
  rank : Tdouble - T = 2 * ((∑ i ∈ labels, bottom i) + J) -
    (∑ i ∈ labels, (bottom i + partner i)) - Ve + V
  fixed : Ve - J ≤ V
  nonnegJ : 0 ≤ J
  partner_le : ∀ i ∈ labels, partner i ≤ bottom i

variable {ι : Type*} (s : Data ι)

theorem odd_rank_bound : (∑ i ∈ s.labels, (s.bottom i + s.partner i)) ≤
    2 * (∑ i ∈ s.labels, s.bottom i) := by
  calc
    _ ≤ ∑ i ∈ s.labels, (s.bottom i + s.bottom i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact add_le_add (le_refl _) (s.partner_le i hi)
    _ = _ := by rw [Finset.sum_add_distrib]; ring

theorem doubling_monotone : s.T ≤ s.Tdouble :=
  Finsler.Budget.doubling_monotone _ _ _ _ _ _ _ s.rank s.fixed s.nonnegJ
    (odd_rank_bound s)

/-- Equality of total defects forces every partner rank to equal its bottom rank. -/
theorem equality_forces_partner (heq : s.Tdouble = s.T) :
    ∀ i ∈ s.labels, s.partner i = s.bottom i := by
  have hodd := (Finsler.Budget.doubling_equality _ _ _ _ _ _ _
    s.rank s.fixed s.nonnegJ (odd_rank_bound s) heq).2
  have hsum : ∑ i ∈ s.labels, (s.bottom i - s.partner i) = 0 := by
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib] at hodd
    linarith
  exact Finsler.Budget.each_partner_of_sum_eq s.labels s.bottom s.partner s.partner_le hsum

/-- A single strict partner gap already forces strict doubling growth. -/
theorem strict_of_partner_gap (i : ι) (hi : i ∈ s.labels)
    (hgap : s.partner i < s.bottom i) : s.T < s.Tdouble := by
  have hmono := doubling_monotone s
  by_contra h
  have heq : s.Tdouble = s.T := by linarith
  have := equality_forces_partner s heq i hi
  linarith

end Finsler.PartnerRank
