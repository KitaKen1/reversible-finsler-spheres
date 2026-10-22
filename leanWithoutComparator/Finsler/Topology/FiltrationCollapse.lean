module

public import Finsler.Topology.GysinPattern

/-! Collapse of the round filtration of the loop space, ordinary and reflection Borel.

A filtration in the form used here consists of involutive complexes Z_m (the sublevel pairs
(t_{c_m}, M) at regular cuts c_m between the critical levels), crossing complexes P_j and
degreewise short exact sequences 0 → P_j → Z_{j+1} → Z_j → 0 (the triples (t_{c_{j+1}}, t_{c_j}, M)),
with Z_0 acyclic, such that every crossing P_j has the pattern of a critical manifold V₂ of index
l_j: ordinary cohomology of dimension at most one in the degrees l_j, l_j + d, l_j + d + 1,
l_j + 2d + 1, starts in the first and third and ends in the second and fourth degree. The indices
satisfy l_{j+1} = l_j + 2d with d ≥ 2 (for the round sphere l_j = (2j + 1)(n − 1), d = n − 1).
For d = 2 one connecting map is not excluded by degrees: from the start class of degree
l_j + d + 1 of Z_{j+1} to the lowest degree l_{j+1} of P_{j+1}; its vanishing (`SpecialAt`; the
start class is the restriction of the global class e X_j) is a hypothesis, automatic for d ≥ 3.

Theorem: at every stage the ordinary and the Borel connecting maps vanish. The ordinary
cohomology of Z_m has dimension at most one, is supported in the degrees of the crossings below m,
and the start and end degrees of the crossings are starts and ends of Z_m. Induction on m: the
ordinary connecting map vanishes on forgetful images by degrees (and the hypothesis for d = 2);
then the Borel connecting map vanishes (`CrossingCollapse.delta_eq_zero`, the starts of Z_m lie
at most in the lowest degree of P_m, where forgetting is injective); then the ordinary connecting
map vanishes on the remaining classes, whose image lies in an end degree of P_m where the
transfer is injective and commutes with the connecting maps. The statuses are transported along
the split sequences. -/

@[expose] public section

namespace Finsler.FiltrationCollapse

open Finsler.BorelCochain Finsler.BorelExact Finsler.CrossingCollapse Finsler.GysinPattern
open Module

noncomputable section

/-- The degrees of a crossing with lowest degree L. -/
def InD (d L q : ℕ) : Prop := q = L ∨ q = L + d ∨ q = L + d + 1 ∨ q = L + d + 1 + d

/-- The start degrees of a crossing with lowest degree L. -/
def StartD (d L q : ℕ) : Prop := q = L ∨ q = L + d + 1

/-- The end degrees of a crossing with lowest degree L. -/
def EndD (d L q : ℕ) : Prop := q = L + d ∨ q = L + d + 1 + d

/-- A filtration with crossings of the pattern of V₂. -/
structure Filtration (d : ℕ) where
  two_le : 2 ≤ d
  l : ℕ → ℕ
  l_succ : ∀ j, l (j + 1) = l j + 2 * d
  Z : ℕ → InvComplex
  P : ℕ → InvComplex
  ι : ∀ j, InvHom (P j) (Z (j + 1))
  π : ∀ j, InvHom (Z (j + 1)) (Z j)
  exact : ∀ j, ShortExact (ι j) (π j)
  zero : ∀ q (z : H (Z 0) q), z = 0
  pattern : ∀ j, Pattern (P j) (l j) d

variable {d : ℕ} (F : Filtration d)

namespace Filtration

theorem l_le_of_lt {j j' : ℕ} (h : j < j') : F.l j + 2 * d ≤ F.l j' := by
  induction j' with
  | zero => omega
  | succ j' ih =>
    rw [F.l_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · have := ih h'
      omega
    · subst h'
      omega

theorem l_add_four_le {j j' : ℕ} (h : j + 1 < j') : F.l j + 4 * d ≤ F.l j' := by
  have h1 := F.l_le_of_lt h
  rw [F.l_succ] at h1
  omega

end Filtration

/-- The one connecting map at the stage m which is not excluded by degrees when d = 2: from the
start degree l_j + d + 1 of Z_{j+1} (m = j + 1) to the next crossing. -/
def SpecialAt (m : ℕ) : Prop :=
  ∀ j, j + 1 = m → ∀ y : HR (F.Z m) (F.l j + d + 1),
    OrdinaryDelta.delta (F.exact m) (F.l j + d + 1) (forget (F.Z m) (F.l j + d + 1) y) = 0

/-- For d ≥ 3 the special connecting map is excluded by degrees. -/
theorem specialAt_of_three_le (h3 : 3 ≤ d) (m : ℕ) : SpecialAt F m := by
  intro j hj y
  subst hj
  apply (F.pattern (j + 1)).supp
  all_goals (have := F.l_succ j; omega)

/-- The inductive statement about the stage m. -/
structure Good (m : ℕ) : Prop where
  fin : ∀ q, FiniteDimensional (ZMod 2) (H (F.Z m) q)
  dim : ∀ q, finrank (ZMod 2) (H (F.Z m) q) ≤ 1
  supp : ∀ q, (∀ j, j < m → ¬ InD d (F.l j) q) → ∀ z : H (F.Z m) q, z = 0
  start : ∀ j, j < m → ∀ q, StartD d (F.l j) q → IsStart (F.Z m) q
  fend : ∀ j, j < m → ∀ q, EndD d (F.l j) q → IsEnd (F.Z m) q
  finR : ∀ q, FiniteDimensional (ZMod 2) (HR (F.Z m) q)

variable {F}

theorem good_zero : Good F 0 where
  fin q := by
    have : Subsingleton (H (F.Z 0) q) := ⟨fun a b => by rw [F.zero q a, F.zero q b]⟩
    infer_instance
  dim q := by
    have : Subsingleton (H (F.Z 0) q) := ⟨fun a b => by rw [F.zero q a, F.zero q b]⟩
    rw [finrank_zero_of_subsingleton]
    omega
  supp q _ := F.zero q
  start j hj := absurd hj (Nat.not_lt_zero j)
  fend j hj := absurd hj (Nat.not_lt_zero j)
  finR q := by
    have h0 : ∀ x : HR (F.Z 0) q, x = 0 :=
      HR_zero_below (l := q + 1) (fun q' _ => F.zero q') q (by omega)
    have : Subsingleton (HR (F.Z 0) q) := ⟨fun a b => by rw [h0 a, h0 b]⟩
    infer_instance

variable {m : ℕ}

/-- A nonzero ordinary class of Z_m lies in a degree of a crossing below m. -/
theorem good_exists_InD (G : Good F m) {q : ℕ} {z : H (F.Z m) q} (hz : z ≠ 0) :
    ∃ j, j < m ∧ InD d (F.l j) q := by
  by_contra h
  push_neg at h
  exact hz (G.supp q h z)

/-- A start of Z_m is a start degree of a crossing below m. -/
theorem good_exists_StartD (G : Good F m) {q : ℕ} (hs : IsStart (F.Z m) q) :
    ∃ j, j < m ∧ StartD d (F.l j) q := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨j, hj, hD⟩ := good_exists_InD G hy
  refine ⟨j, hj, ?_⟩
  have := G.fin q
  rcases hD with h | h | h | h
  · exact Or.inl h
  · exact absurd (G.fend j hj q (Or.inl h)) (not_end_of_start (G.dim q) ⟨y, hy⟩)
  · exact Or.inr h
  · exact absurd (G.fend j hj q (Or.inr h)) (not_end_of_start (G.dim q) ⟨y, hy⟩)

/-- The ordinary cohomology of the crossing P_m vanishes outside its degrees. -/
theorem P_zero {q : ℕ} (h : ¬ InD d (F.l m) q) (z : H (F.P m) q) : z = 0 := by
  simp only [InD, not_or] at h
  exact (F.pattern m).supp q h.1 h.2.1 h.2.2.1 h.2.2.2 z

/-- The ordinary connecting map vanishes on forgetful images. -/
theorem good_delta_ord_forget (G : Good F m) (hs : SpecialAt F m) (q : ℕ) (y : HR (F.Z m) q) :
    OrdinaryDelta.delta (F.exact m) q (forget (F.Z m) q y) = 0 := by
  have hd := F.two_le
  by_cases hy : forget (F.Z m) q y = 0
  · rw [hy, map_zero]
  by_cases hD : InD d (F.l m) (q + 1)
  · obtain ⟨j, hj, hq⟩ := good_exists_InD G hy
    obtain ⟨j', hj'⟩ := good_exists_StartD G ⟨y, hy⟩
    rcases Nat.lt_or_ge (j + 1) m with hjm | hjm
    · have h4 := F.l_add_four_le hjm
      exfalso
      rcases hq with h | h | h | h <;> rcases hD with h' | h' | h' | h' <;> omega
    · have hm : m = j + 1 := by omega
      subst hm
      have hl := F.l_succ j
      have := G.fin q
      rcases hq with h | h | h | h <;> rcases hD with h' | h' | h' | h'
      all_goals first
        | (exfalso; omega)
        | skip
      · -- q = l j + d + 1, q + 1 = l (j + 1), d = 2
        subst h
        exact hs j rfl y
      · -- q = l j + 2d + 1 is an end degree
        exact absurd (G.fend j (by omega) q (Or.inr h))
          (not_end_of_start (G.dim q) ⟨y, hy⟩)
  · exact P_zero hD _

/-- The Borel connecting map vanishes. -/
theorem good_delta_zero (G : Good F m) (hs : SpecialAt F m) :
    ∀ q (x : HR (F.Z m) q), delta (F.exact m) q x = 0 := by
  apply delta_eq_zero (F.exact m) G.fin G.dim (good_delta_ord_forget G hs)
  intro q hs
  obtain ⟨j, hj, hq⟩ := good_exists_StartD G hs
  have hl := F.l_le_of_lt hj
  have hd := F.two_le
  have hq1 : q + 1 ≤ F.l m := by rcases hq with h | h <;> omega
  rcases Nat.lt_or_ge (q + 1) (F.l m) with hlt | hge
  · intro a b _
    rw [(F.pattern m).HR_below (q + 1) hlt a, (F.pattern m).HR_below (q + 1) hlt b]
  · have he : q + 1 = F.l m := le_antisymm hq1 hge
    rw [he]
    exact (F.pattern m).forget_injective_low

/-- The ordinary connecting map vanishes. -/
theorem good_delta_ord_zero (G : Good F m) (hs : SpecialAt F m) :
    ∀ q (x : H (F.Z m) q), OrdinaryDelta.delta (F.exact m) q x = 0 := by
  intro q x
  have hd := F.two_le
  by_cases hx : x = 0
  · rw [hx, map_zero]
  by_cases hD : InD d (F.l m) (q + 1)
  · obtain ⟨j, hj, hq⟩ := good_exists_InD G hx
    have := G.fin q
    -- if q is a start, x is a forgetful image
    by_cases hst : IsStart (F.Z m) q
    · obtain ⟨y₀, hy₀⟩ := hst
      obtain ⟨c, rfl⟩ := TowerSpan.exists_smul_of_finrank_le_one (G.dim q) hy₀ x
      rw [← map_smul, good_delta_ord_forget G hs]
    · -- otherwise q + 1 is an end of P_m, where the transfer is injective
      rcases Nat.lt_or_ge (j + 1) m with hjm | hjm
      · have h4 := F.l_add_four_le hjm
        exfalso
        rcases hq with h | h | h | h <;> rcases hD with h' | h' | h' | h' <;> omega
      · have hm : m = j + 1 := by omega
        subst hm
        have hl := F.l_succ j
        have hend : IsEnd (F.P (j + 1)) (q + 1) := by
          rcases hq with h | h | h | h <;> rcases hD with h' | h' | h' | h'
          all_goals first
            | (exfalso; omega)
            | skip
          · exact absurd (G.start j (by omega) q (Or.inr h)) hst
          · rw [show q + 1 = F.l (j + 1) + d by omega]
            exact (F.pattern (j + 1)).end₁
        have := (F.pattern (j + 1)).fin (q + 1)
        apply transfer_injective_of_end ((F.pattern (j + 1)).dim (q + 1)) hend
        rw [← delta_transfer, good_delta_zero G hs, map_zero]
  · exact P_zero hD _

/-- The step of the induction. -/
theorem good_succ (G : Good F m) (hs : SpecialAt F m) : Good F (m + 1) := by
  have hd := F.two_le
  have hδ := good_delta_zero G hs
  have hδo := good_delta_ord_zero G hs
  have hPfin := (F.pattern m).fin
  have hPfinR := finite_HR hPfin
  have hfin : ∀ q, FiniteDimensional (ZMod 2) (H (F.Z (m + 1)) q) := fun q => by
    have := hPfin q
    have := G.fin q
    exact TameHomology.finite_of_exact_linear (Hmap (F.ι m) q) (Hmap (F.π m) q)
      fun x hx => exact_mid_ordinary (F.exact m) q x hx
  -- disjointness of the degrees of P_m and of the crossings below m
  have hdisj : ∀ q, InD d (F.l m) q → ∀ j, j < m → ¬ InD d (F.l j) q := by
    intro q hq j hj hqj
    rcases Nat.lt_or_ge (j + 1) m with hjm | hjm
    · have h4 := F.l_add_four_le hjm
      rcases hq with h | h | h | h <;> rcases hqj with h' | h' | h' | h' <;> omega
    · have hm : m = j + 1 := by omega
      subst hm
      have hl := F.l_succ j
      rcases hq with h | h | h | h <;> rcases hqj with h' | h' | h' | h' <;> omega
  refine ⟨hfin, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have := G.fin q
    have := hPfin q
    have := hfin q
    rw [finrank_eq_add_ordinary hδo q]
    by_cases hq : InD d (F.l m) q
    · have h0 : finrank (ZMod 2) (H (F.Z m) q) = 0 := by
        rw [finrank_eq_zero_iff]
        intro z
        exact ⟨1, one_ne_zero, by rw [one_smul, G.supp q (hdisj q hq) z]⟩
      have := (F.pattern m).dim q
      omega
    · have h0 : finrank (ZMod 2) (H (F.P m) q) = 0 := by
        rw [finrank_eq_zero_iff]
        intro z
        exact ⟨1, one_ne_zero, by rw [one_smul, P_zero hq z]⟩
      have := G.dim q
      omega
  · intro q hq z
    have hP : ¬ InD d (F.l m) q := hq m (Nat.lt_succ_self m)
    have hZ : ∀ j, j < m → ¬ InD d (F.l j) q := fun j hj => hq j (by omega)
    obtain ⟨z', hz'⟩ := exact_mid_ordinary (F.exact m) q z (G.supp q hZ _)
    rw [← hz', P_zero hP z', map_zero]
  · intro j hj q hq
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact isStart_of_map (F.π m) (surjective_of_delta hδ q) (G.start j hj' q hq)
    · subst hj'
      apply isStart_map (F.ι j) (injective_of_delta_ordinary hδo q)
      rcases hq with h | h
      · subst h
        exact ⟨(F.pattern j).τ, (F.pattern j).forget_τ⟩
      · subst h
        exact ⟨(F.pattern j).σ, (F.pattern j).forget_σ⟩
  · intro j hj q hq
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact isEnd_of_map (F.π m) (surjective_of_delta_ordinary hδo q) (G.fend j hj' q hq)
    · subst hj'
      apply isEnd_map (F.ι j) (injective_of_delta hδ q)
      rcases hq with h | h
      · subst h
        exact (F.pattern j).end₁
      · subst h
        exact (F.pattern j).end₂
  · intro q
    have := hPfinR q
    have := G.finR q
    exact TameHomology.finite_of_exact_linear (HRmap (F.ι m) q) (HRmap (F.π m) q)
      fun x hx => exact_mid (F.exact m) q x hx

variable (F)

/-- Every stage of the filtration is good if the special connecting maps vanish. -/
theorem good (hs : ∀ m, SpecialAt F m) : ∀ m, Good F m
  | 0 => good_zero
  | m + 1 => good_succ (good hs m) (hs m)

/-- The ordinary crossing sequences collapse. -/
theorem delta_ord_eq_zero (hs : ∀ m, SpecialAt F m) (m q : ℕ) (x : H (F.Z m) q) :
    OrdinaryDelta.delta (F.exact m) q x = 0 :=
  good_delta_ord_zero (good F hs m) (hs m) q x

/-- The reflection Borel crossing sequences collapse. -/
theorem delta_eq_zero (hs : ∀ m, SpecialAt F m) (m q : ℕ) (x : HR (F.Z m) q) :
    delta (F.exact m) q x = 0 :=
  good_delta_zero (good F hs m) (hs m) q x

end

end Finsler.FiltrationCollapse
