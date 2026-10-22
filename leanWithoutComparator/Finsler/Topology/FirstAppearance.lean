module

public import Finsler.Algebra.PartnerRank
public import Lean.Elab.Tactic.Omega

/-! First appearance in a finite sequence of cuts, with a natural local cup
action and the doubling rank formula. All maps, exactness and rank hypotheses
are explicit. No Finsler sublevel or Borel model is constructed by this file. -/

@[expose] public section

namespace Finsler.FirstAppearance

/-- Direct least-index extraction: no search over cohomology classes is needed. -/
theorem exists_first {P : ℕ → Prop} (m : ℕ) (hzero : ¬ P 0) (hm : P m) :
    ∃ i, i < m ∧ ¬ P i ∧ P (i + 1) := by
  classical
  have hex : ∃ k, P k := ⟨m, hm⟩
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex hm
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    exact hzero (hk0 ▸ hk)
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · exact Nat.find_min hex (by omega)
  · have hs : k - 1 + 1 = k := by omega
    simpa only [hs] using hk

universe u

variable (G : Type u) (V W C E : ℕ → Type u)
  [AddCommGroup G] [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
  [∀ i, AddCommGroup (C i)] [∀ i, AddCommGroup (E i)]

/-- The relevant part of a relative exact sequence and a natural cup action. -/
structure Data where
  restrict : ∀ i, V (i + 1) →+ V i
  res : ∀ i, G →+ V i
  crossing : ∀ i, C i →+ V (i + 1)
  cup : ∀ i, V i →+ W i
  localCup : ∀ i, C i →+ E i
  crossingCup : ∀ i, E i →+ W (i + 1)
  natural_res : ∀ i x, restrict i (res (i + 1) x) = res i x
  exact_crossing : ∀ i x, restrict i x = 0 → ∃ z, crossing i z = x
  natural_cup : ∀ i z, cup (i + 1) (crossing i z) = crossingCup i (localCup i z)

variable {G V W C E} (s : Data G V W C E)

noncomputable def bottom (x : G) (i : ℕ) : ℤ := by
  classical
  exact if s.res i x = 0 then 0 else 1

noncomputable def partner (x : G) (i : ℕ) : ℤ := by
  classical
  exact if s.cup i (s.res i x) = 0 then 0 else 1

theorem partner_le_bottom (x : G) (i : ℕ) : partner s x i ≤ bottom s x i := by
  classical
  by_cases h : s.res i x = 0
  · simp [partner, bottom, h]
  · simp only [partner, bottom, ite_eq_right h]
    split <;> norm_num

/-- Exactness supplies a crossing class; naturality transfers local cup vanishing. -/
theorem first_cup_zero (x : G) (m : ℕ)
    (hzero : s.res 0 x = 0) (hm : s.res m x ≠ 0)
    (local_zero : ∀ i, i < m → ∀ z, s.localCup i z = 0) :
    ∃ i, i < m ∧ s.res i x = 0 ∧ s.res (i + 1) x ≠ 0 ∧
      s.cup (i + 1) (s.res (i + 1) x) = 0 := by
  obtain ⟨i, hi, hprev, hnext⟩ := exists_first (P := fun i => s.res i x ≠ 0)
    m (by simpa using hzero) hm
  have hprev' : s.res i x = 0 := by simpa using hprev
  have hr : s.restrict i (s.res (i + 1) x) = 0 := by rw [s.natural_res, hprev']
  obtain ⟨z, hz⟩ := s.exact_crossing i _ hr
  refine ⟨i, hi, hprev', hnext, ?_⟩
  rw [← hz, s.natural_cup, local_zero i hi z, map_zero]

theorem first_partner_gap (x : G) (m : ℕ)
    (hzero : s.res 0 x = 0) (hm : s.res m x ≠ 0)
    (local_zero : ∀ i, i < m → ∀ z, s.localCup i z = 0) :
    ∃ i, i < m ∧ bottom s x (i + 1) = 1 ∧ partner s x (i + 1) = 0 := by
  classical
  obtain ⟨i, hi, _, hb, hp⟩ := first_cup_zero s x m hzero hm local_zero
  exact ⟨i, hi, by simp [bottom, hb], by simp [partner, hp]⟩

/-- The finite crossing argument composed with the numerical doubling formula.
The budgets must be realized at the successor cuts; their distinguished labels
are identified with the actual restrictions of x and its cup partner. -/
theorem not_visible_of_doubling_plateau {ι : Type*} (x : G) (m : ℕ)
    (budgets : ℕ → Finsler.PartnerRank.Data ι) (label : ℕ → ι)
    (hzero : s.res 0 x = 0)
    (local_zero : ∀ i, i < m → ∀ z, s.localCup i z = 0)
    (member : ∀ i, i < m → label i ∈ (budgets i).labels)
    (bottom_rank : ∀ i, i < m → (budgets i).bottom (label i) = bottom s x (i + 1))
    (partner_rank : ∀ i, i < m → (budgets i).partner (label i) = partner s x (i + 1))
    (plateau : ∀ i, i < m → (budgets i).Tdouble = (budgets i).T) :
    s.res m x = 0 := by
  by_contra hm
  obtain ⟨i, hi, hb, hp⟩ := first_partner_gap s x m hzero hm local_zero
  have heq := Finsler.PartnerRank.equality_forces_partner (budgets i)
    (plateau i hi) (label i) (member i hi)
  rw [bottom_rank i hi, partner_rank i hi, hb, hp] at heq
  norm_num at heq

end Finsler.FirstAppearance
