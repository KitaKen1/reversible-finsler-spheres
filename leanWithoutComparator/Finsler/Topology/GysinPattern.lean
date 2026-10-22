module

public import Finsler.Topology.CrossingCollapse
public import Finsler.Topology.GysinCount
public import Finsler.Topology.NilpotentW

/-! The reflection Borel cohomology of a crossing group from its ordinary cohomology.

Let the ordinary cohomology of an involutive complex P have dimension at most one in every degree
and vanish outside the degrees l, l + d, l + d + 1 and l + 2d + 1 (d ≥ 1); these are the degrees
of the crossing group of a critical manifold V₂(ℝⁿ⁺¹) of index l, d = n − 1. Let τ in degree l and
σ in degree l + d + 1 be Borel classes with nonzero forgetful images (in the application σ = e τ).

If the Borel cohomology of P vanishes in some degree above l + 2d + 1 (w is nilpotent), the
degrees l + d and l + 2d + 1 are ends of the Gysin sequence. Indeed, by the dimension count of
the Gysin sequence the total ordinary dimension is twice the total dimension of the kernels of
w; the ordinary dimension at a degree is the rank of forgetting plus the dimension of the kernel
of w; the two starts contribute rank 2 and no kernel, so the two other degrees carry a kernel of
w each.

Given the two ends, the Borel cohomology is two towers of length d + 1: it vanishes below l, is
spanned by w^k τ in degree l + k and by w^k σ in degree l + d + 1 + k for k ≤ d, vanishes above
l + 2d + 1, the classes w^d τ and w^d σ are nonzero and w^{d+1} τ = w^{d+1} σ = 0. The proof
walks up the degrees: where ordinary cohomology vanishes or the degree is an end, forgetting is
zero and every class is a w-multiple; at an end the spanning class is the nonzero class killed
by w; above a degree where w vanishes, forgetting is injective, so the start class spans. -/

@[expose] public section

namespace Finsler.GysinPattern

open Finsler.BorelCochain Finsler.CrossingCollapse Finsler.NilpotentW Module

noncomputable section

variable {P : InvComplex}

/-! ### One degree at a time -/

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- If forgetting vanishes in degree q + 1 and HR^q is spanned by y, then HR^{q+1} is spanned
by w y. -/
theorem span_w {q : ℕ} {y : HR P q} (hspan : ∀ x : HR P q, ∃ c : ZMod 2, x = c • y)
    (hf : ∀ x : HR P (q + 1), forget P (q + 1) x = 0) :
    ∀ x : HR P (q + 1), ∃ c : ZMod 2, x = c • w P q y := by
  intro x
  obtain ⟨y', rfl⟩ := (exact_forget P q x).mp (hf x)
  obtain ⟨c, rfl⟩ := hspan y'
  exact ⟨c, map_smul _ _ _⟩

/-- Where w vanishes on HR^q, forgetting is injective on HR^{q+1}. -/
theorem forget_injective_of_w {q : ℕ} (hw : ∀ x : HR P q, w P q x = 0) :
    Function.Injective (forget P (q + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_forget P q x).mp hx
  exact hw y

/-- Where forgetting is injective and ordinary cohomology has dimension at most one, a class
with nonzero forgetful image spans. -/
theorem span_of_forget {q : ℕ} [FiniteDimensional (ZMod 2) (H P q)]
    (hdim : finrank (ZMod 2) (H P q) ≤ 1) (hinj : Function.Injective (forget P q))
    {σ : HR P q} (hσ : forget P q σ ≠ 0) : ∀ x : HR P q, ∃ c : ZMod 2, x = c • σ := by
  intro x
  obtain ⟨c, hc⟩ := TowerSpan.exists_smul_of_finrank_le_one hdim hσ (forget P q x)
  exact ⟨c, hinj (by rw [hc, map_smul])⟩

/-- At an end, the spanning class is nonzero and killed by w. -/
theorem end_spanning {q : ℕ} {y : HR P q} (hspan : ∀ x : HR P q, ∃ c : ZMod 2, x = c • y)
    (he : IsEnd P q) : y ≠ 0 ∧ w P q y = 0 := by
  obtain ⟨t, ht, hwt⟩ := (isEnd_iff q).mp he
  obtain ⟨c, rfl⟩ := hspan t
  have hc : c = 1 := by
    fin_cases c
    · exact absurd (zero_smul _ y) ht
    · rfl
  rw [hc, one_smul] at ht hwt
  exact ⟨ht, hwt⟩

/-- At an end of ordinary dimension at most one the transfer is injective. -/
theorem transfer_injective_of_end {q : ℕ} [FiniteDimensional (ZMod 2) (H P q)]
    (hdim : finrank (ZMod 2) (H P q) ≤ 1) (he : IsEnd P q) :
    Function.Injective (transfer P q) := by
  obtain ⟨z₀, hz₀⟩ := he
  have hne : z₀ ≠ 0 := fun h0 => hz₀ (by rw [h0, map_zero])
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨c, rfl⟩ := TowerSpan.exists_smul_of_finrank_le_one hdim hne z
  rw [map_smul] at hz
  rcases zmod2_eq_zero_or_one c with hc | hc
  · rw [hc, zero_smul]
  · rw [hc, one_smul] at hz
    exact absurd hz hz₀

/-- At a degree of ordinary dimension at most one which is an end, forgetting vanishes. -/
theorem forget_zero_of_end {q : ℕ} [FiniteDimensional (ZMod 2) (H P q)]
    (hdim : finrank (ZMod 2) (H P q) ≤ 1) (he : IsEnd P q) :
    ∀ x : HR P q, forget P q x = 0 := by
  intro x
  by_contra hx
  exact not_end_of_start hdim ⟨x, hx⟩ he

/-- Vanishing of HR^q and of ordinary cohomology in degree q + 1 gives vanishing of HR^{q+1}. -/
theorem zero_succ {q : ℕ} (h0 : ∀ x : HR P q, x = 0) (hH : ∀ z : H P (q + 1), z = 0) :
    ∀ x : HR P (q + 1), x = 0 := by
  intro x
  obtain ⟨y, rfl⟩ := (exact_forget P q x).mp (hH _)
  rw [h0 y, map_zero]

/-- Below the first degree of ordinary cohomology the Borel cohomology vanishes. -/
theorem HR_zero_below {l : ℕ} (hH : ∀ q, q < l → ∀ z : H P q, z = 0) :
    ∀ q, q < l → ∀ x : HR P q, x = 0 := by
  intro q
  induction q with
  | zero =>
    intro hq x
    apply BorelQuasiIso.forget_zero_injective P
    rw [hH 0 hq (forget P 0 x), map_zero]
  | succ q ih =>
    intro hq
    exact zero_succ (ih (by omega)) (hH (q + 1) hq)

/-- Above a degree where HR vanishes and ordinary cohomology vanishes, HR vanishes. -/
theorem HR_zero_above {Q : ℕ} (h0 : ∀ x : HR P Q, x = 0)
    (hH : ∀ q, Q < q → ∀ z : H P q, z = 0) : ∀ q, Q ≤ q → ∀ x : HR P q, x = 0 := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => exact h0
  | succ q hq ih => exact zero_succ ih (hH (q + 1) (by omega))

/-! ### Towers -/

/-- A tower: if HR^{lo} is spanned by y and forgetting vanishes in the degrees lo + 1, …, lo + k,
then HR^{lo+k} is spanned by w^k y. -/
theorem span_wPow {lo : ℕ} {y : HR P lo} (hspan : ∀ x : HR P lo, ∃ c : ZMod 2, x = c • y) :
    ∀ k : ℕ, (∀ j, 1 ≤ j → j ≤ k → ∀ x : HR P (lo + j), forget P (lo + j) x = 0) →
      ∀ x : HR P (lo + k), ∃ c : ZMod 2, x = c • wPow P lo k y := by
  intro k
  induction k with
  | zero =>
    intro _
    exact hspan
  | succ k ih =>
    intro hf
    have hk := ih fun j hj1 hjk => hf j hj1 (by omega)
    exact span_w hk (hf (k + 1) (by omega) le_rfl)

/-- A vanishing power of w stays zero. -/
theorem wPow_zero_add {lo k : ℕ} {y : HR P lo} (h : wPow P lo k y = 0) :
    ∀ j, wPow P lo (k + j) y = 0
  | 0 => h
  | j + 1 => by rw [show k + (j + 1) = k + j + 1 from rfl, wPow_succ, wPow_zero_add h j, map_zero]

/-- A vanishing power of w stays zero. -/
theorem wPow_zero_of_le {lo k m : ℕ} {y : HR P lo} (h : wPow P lo k y = 0) (hkm : k ≤ m) :
    wPow P lo m y = 0 := by
  have := wPow_zero_add h (m - k)
  rwa [Nat.add_sub_cancel' hkm] at this

/-- The pattern of a crossing group: ordinary cohomology of dimension at most one supported in
four degrees, two start classes and two ends. -/
structure Pattern (P : InvComplex) (l d : ℕ) where
  one_le : 1 ≤ d
  fin : ∀ q, FiniteDimensional (ZMod 2) (H P q)
  dim : ∀ q, finrank (ZMod 2) (H P q) ≤ 1
  supp : ∀ q, q ≠ l → q ≠ l + d → q ≠ l + d + 1 → q ≠ l + d + 1 + d → ∀ z : H P q, z = 0
  τ : HR P l
  forget_τ : forget P l τ ≠ 0
  σ : HR P (l + d + 1)
  forget_σ : forget P (l + d + 1) σ ≠ 0
  end₁ : IsEnd P (l + d)
  end₂ : IsEnd P (l + d + 1 + d)

namespace Pattern

variable {l d : ℕ} (A : Pattern P l d)
include A

theorem HR_below : ∀ q, q < l → ∀ x : HR P q, x = 0 :=
  HR_zero_below fun q hq => A.supp q (by omega) (by have := A.one_le; omega)
    (by omega) (by omega)

/-- Forgetting is injective in the lowest degree. -/
theorem forget_injective_low : Function.Injective (forget P l) := by
  cases l with
  | zero => exact BorelQuasiIso.forget_zero_injective P
  | succ l =>
    exact forget_injective_of_w fun x => by rw [A.HR_below l (by omega) x, map_zero]

theorem span_τ : ∀ x : HR P l, ∃ c : ZMod 2, x = c • A.τ := by
  have := A.fin l
  exact span_of_forget (A.dim l) A.forget_injective_low A.forget_τ

/-- Forgetting vanishes in the degrees l + 1, …, l + d. -/
theorem forget_bottom (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d) (x : HR P (l + j)) :
    forget P (l + j) x = 0 := by
  rcases Nat.lt_or_ge j d with hj | hj
  · rw [A.supp (l + j) (by omega) (by omega) (by omega) (by omega) (forget P (l + j) x)]
  · have hjd' : j = d := le_antisymm hjd hj
    subst hjd'
    have := A.fin (l + j)
    exact forget_zero_of_end (A.dim (l + j)) A.end₁ x

/-- The bottom tower spans: HR^{l+k} is spanned by w^k τ for k ≤ d. -/
theorem span_bottom (k : ℕ) (hk : k ≤ d) :
    ∀ x : HR P (l + k), ∃ c : ZMod 2, x = c • wPow P l k A.τ :=
  span_wPow A.span_τ k fun j hj1 hjk => A.forget_bottom j hj1 (by omega)

theorem bottom_end : wPow P l d A.τ ≠ 0 ∧ w P (l + d) (wPow P l d A.τ) = 0 :=
  end_spanning (A.span_bottom d le_rfl) A.end₁

/-- The top of the bottom tower is nonzero. -/
theorem bottom_top_ne : wPow P l d A.τ ≠ 0 := A.bottom_end.1

/-- The bottom tower has length d + 1. -/
theorem bottom_vanish : wPow P l (d + 1) A.τ = 0 := A.bottom_end.2

/-- The bottom tower classes are nonzero. -/
theorem bottom_ne (k : ℕ) (hk : k ≤ d) : wPow P l k A.τ ≠ 0 :=
  fun h0 => A.bottom_top_ne (wPow_zero_of_le h0 hk)

theorem w_zero_bottom_top : ∀ x : HR P (l + d), w P (l + d) x = 0 := by
  intro x
  obtain ⟨c, rfl⟩ := A.span_bottom d le_rfl x
  rw [map_smul, A.bottom_end.2, smul_zero]

theorem span_σ : ∀ x : HR P (l + d + 1), ∃ c : ZMod 2, x = c • A.σ := by
  have := A.fin (l + d + 1)
  exact span_of_forget (A.dim _) (forget_injective_of_w A.w_zero_bottom_top) A.forget_σ

/-- Forgetting vanishes in the degrees l + d + 2, …, l + 2d + 1. -/
theorem forget_top (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d) (x : HR P (l + d + 1 + j)) :
    forget P (l + d + 1 + j) x = 0 := by
  rcases Nat.lt_or_ge j d with hj | hj
  · rw [A.supp (l + d + 1 + j) (by omega) (by omega) (by omega) (by omega)
      (forget P (l + d + 1 + j) x)]
  · have hjd' : j = d := le_antisymm hjd hj
    subst hjd'
    have := A.fin (l + j + 1 + j)
    exact forget_zero_of_end (A.dim _) A.end₂ x

/-- The top tower spans: HR^{l+d+1+k} is spanned by w^k σ for k ≤ d. -/
theorem span_top (k : ℕ) (hk : k ≤ d) :
    ∀ x : HR P (l + d + 1 + k), ∃ c : ZMod 2, x = c • wPow P (l + d + 1) k A.σ :=
  span_wPow A.span_σ k fun j hj1 hjk => A.forget_top j hj1 (by omega)

theorem top_end : wPow P (l + d + 1) d A.σ ≠ 0 ∧
    w P (l + d + 1 + d) (wPow P (l + d + 1) d A.σ) = 0 :=
  end_spanning (A.span_top d le_rfl) A.end₂

/-- The top tower has length d + 1. -/
theorem top_vanish : wPow P (l + d + 1) (d + 1) A.σ = 0 := A.top_end.2

/-- The top tower classes are nonzero. -/
theorem top_ne (k : ℕ) (hk : k ≤ d) : wPow P (l + d + 1) k A.σ ≠ 0 :=
  fun h0 => A.top_end.1 (wPow_zero_of_le h0 hk)

/-- Above the top degree the Borel cohomology vanishes. -/
theorem HR_above : ∀ q, l + d + 1 + d < q → ∀ x : HR P q, x = 0 := by
  have h1 : ∀ x : HR P (l + d + 1 + d + 1), x = 0 := by
    have hspan := span_w (A.span_top d le_rfl) fun x =>
      A.supp _ (by omega) (by omega) (by omega) (by omega) _
    intro x
    obtain ⟨c, rfl⟩ := hspan x
    rw [A.top_end.2, smul_zero]
  intro q hq
  exact HR_zero_above h1 (fun q' hq' => A.supp q' (by omega) (by omega) (by omega) (by omega))
    q (by omega)

end Pattern

/-! ### The ends from the vanishing of high-degree Borel cohomology -/

section Ends

variable {l d : ℕ}

theorem finite_HR (hfin : ∀ q, FiniteDimensional (ZMod 2) (H P q)) :
    ∀ q, Module.Finite (ZMod 2) (HR P q) := by
  intro q
  induction q with
  | zero =>
    have := hfin 0
    exact Module.Finite.of_injective (forget P 0) (BorelQuasiIso.forget_zero_injective P)
  | succ q ih =>
    have := hfin (q + 1)
    exact TameHomology.finite_of_exact_linear (w P q) (forget P (q + 1))
      fun x hx => (exact_forget P q x).mp hx

/-- A sum over an initial segment of a function supported in four distinct degrees. -/
theorem sum_four (g : ℕ → ℕ) (Q a b c e : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (ha : a ≤ Q) (hb : b ≤ Q) (hc : c ≤ Q)
    (he : e ≤ Q) (hg : ∀ q, q ≠ a → q ≠ b → q ≠ c → q ≠ e → g q = 0) :
    ∑ q ∈ Finset.range (Q + 1), g q = g a + g b + g c + g e := by
  have hsub : ({a, b, c, e} : Finset ℕ) ⊆ Finset.range (Q + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub fun x _ hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hg x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2]
  rw [Finset.sum_insert (by simp [hab, hac, hae]), Finset.sum_insert (by simp [hbc, hbe]),
    Finset.sum_pair hce]
  ring

/-- If the Borel cohomology vanishes in a degree above the support, the two other degrees of
the support are ends. -/
theorem ends_of_vanishing (hd : 1 ≤ d) (hfin : ∀ q, FiniteDimensional (ZMod 2) (H P q))
    (hdim : ∀ q, finrank (ZMod 2) (H P q) ≤ 1)
    (hsupp : ∀ q, q ≠ l → q ≠ l + d → q ≠ l + d + 1 → q ≠ l + d + 1 + d → ∀ z : H P q, z = 0)
    {τ : HR P l} (hτ : forget P l τ ≠ 0) {σ : HR P (l + d + 1)}
    (hσ : forget P (l + d + 1) σ ≠ 0) {Q : ℕ} (hQ : l + d + 1 + d < Q)
    (hvan : ∀ x : HR P Q, x = 0) : IsEnd P (l + d) ∧ IsEnd P (l + d + 1 + d) := by
  have := hfin
  have := finite_HR hfin
  have hzero : ∀ q, l + d + 1 + d + 1 ≤ q → ∀ z : H P q, z = 0 := fun q hq =>
    hsupp q (by omega) (by omega) (by omega) (by omega)
  have hcount := GysinCount.total_count hzero Q (by omega)
  have hHR : finrank (ZMod 2) (HR P Q) = 0 := by
    rw [finrank_eq_zero_iff]
    intro x
    exact ⟨1, one_ne_zero, by rw [one_smul, hvan x]⟩
  -- f q = rank of forgetting, k q = dimension of the kernel of w
  set f : ℕ → ℕ := fun q => finrank (ZMod 2) (LinearMap.range (forget P q)) with hfdef
  set k : ℕ → ℕ := fun q => finrank (ZMod 2) (LinearMap.ker (w P q)) with hkdef
  have hHq : ∀ q, finrank (ZMod 2) (H P q) = f q + k q := fun q => GysinCount.finrank_H P q
  have hsum : ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (H P q) =
      ∑ q ∈ Finset.range (Q + 1), f q + ∑ q ∈ Finset.range (Q + 1), k q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => hHq q
  have hoff : ∀ q, q ≠ l → q ≠ l + d → q ≠ l + d + 1 → q ≠ l + d + 1 + d →
      finrank (ZMod 2) (H P q) = 0 := by
    intro q h1 h2 h3 h4
    rw [finrank_eq_zero_iff]
    intro z
    exact ⟨1, one_ne_zero, by rw [one_smul, hsupp q h1 h2 h3 h4 z]⟩
  have hfoff : ∀ q, q ≠ l → q ≠ l + d → q ≠ l + d + 1 → q ≠ l + d + 1 + d → f q = 0 :=
    fun q h1 h2 h3 h4 => by have := hHq q; have := hoff q h1 h2 h3 h4; omega
  have hkoff : ∀ q, q ≠ l → q ≠ l + d → q ≠ l + d + 1 → q ≠ l + d + 1 + d → k q = 0 :=
    fun q h1 h2 h3 h4 => by have := hHq q; have := hoff q h1 h2 h3 h4; omega
  have hfpos : ∀ {q} {y : HR P q}, forget P q y ≠ 0 → 1 ≤ f q := by
    intro q y hy
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [hfdef] at h0
    simp only at h0
    rw [Submodule.finrank_eq_zero] at h0
    apply hy
    have : forget P q y ∈ LinearMap.range (forget P q) := ⟨y, rfl⟩
    rw [h0] at this
    exact (Submodule.mem_bot (ZMod 2)).mp this
  have h1 := hfpos hτ
  have h2 := hfpos hσ
  have hl := hdim l
  have hl2 := hdim (l + d + 1)
  have hm1 := hdim (l + d)
  have hm2 := hdim (l + d + 1 + d)
  rw [hHq] at hl hl2 hm1 hm2
  have hsf := sum_four f Q l (l + d) (l + d + 1) (l + d + 1 + d) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hfoff
  have hsk := sum_four k Q l (l + d) (l + d + 1) (l + d + 1 + d) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hkoff
  rw [hsum, hsf, hsk, hHR] at hcount
  have hk1 : 1 ≤ k (l + d) := by omega
  have hk2 : 1 ≤ k (l + d + 1 + d) := by omega
  have hend : ∀ q, 1 ≤ k q → IsEnd P q := by
    intro q hq
    rw [isEnd_iff]
    have hne : LinearMap.ker (w P q) ≠ ⊥ := by
      intro h0
      rw [hkdef] at hq
      simp only at hq
      rw [h0, finrank_bot] at hq
      omega
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨t, ht0, LinearMap.mem_ker.mp ht⟩
  exact ⟨hend _ hk1, hend _ hk2⟩

/-- A pattern from the vanishing of high-degree Borel cohomology. -/
def patternOfVanishing (hd : 1 ≤ d) (hfin : ∀ q, FiniteDimensional (ZMod 2) (H P q))
    (hdim : ∀ q, finrank (ZMod 2) (H P q) ≤ 1)
    (hsupp : ∀ q, q ≠ l → q ≠ l + d → q ≠ l + d + 1 → q ≠ l + d + 1 + d → ∀ z : H P q, z = 0)
    (τ : HR P l) (hτ : forget P l τ ≠ 0) (σ : HR P (l + d + 1))
    (hσ : forget P (l + d + 1) σ ≠ 0) {Q : ℕ} (hQ : l + d + 1 + d < Q)
    (hvan : ∀ x : HR P Q, x = 0) : Pattern P l d where
  one_le := hd
  fin := hfin
  dim := hdim
  supp := hsupp
  τ := τ
  forget_τ := hτ
  σ := σ
  forget_σ := hσ
  end₁ := (ends_of_vanishing hd hfin hdim hsupp hτ hσ hQ hvan).1
  end₂ := (ends_of_vanishing hd hfin hdim hsupp hτ hσ hQ hvan).2

end Ends

end

end Finsler.GysinPattern
