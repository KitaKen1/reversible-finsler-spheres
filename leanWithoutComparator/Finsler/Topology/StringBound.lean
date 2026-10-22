module

public import Finsler.Topology.GradedLadder
public import Finsler.Topology.OperatorK

/-! A string of powers of w against two cutoffs. Let G be a graded F₂-vector space with a
degree-one operator w and finite dimensional total, and let A be a second graded space with
degree-one operators v and w and comparison maps e(q, l) : A_q → G_l such that v leaves the
components unchanged, w raises the root degree l by one, and the root degree zero component of a
w-multiple vanishes. Let y be a string: classes y_l ≠ 0 with w y_l = y_{l+1} for l in
[L₀, L₀ + ν + q). Then for a cutoff j ≥ L₀ + ν − 1, a degree d, numbers q, m and a cutoff
j' < L₀ + q,

  ν ≤ (dim P_j(G) − dim P_j(e(A_d))) + dim (e(A_{d+q+m}) ∩ ker P_{j'}),

where P_j is the truncation to root degrees at most j. Indeed, the ν classes y_l, l in
[L₀, L₀ + ν), span a subspace of P_j(G) which meets P_j(e(A_d)) in dimension at least ν minus the
first term; lifts of these classes to A_d, multiplied by w^q and v^m, have comparison images
w^q(y_l) + (terms of higher root degree), which are independent and vanish in root degrees at
most j'. This is the step which turns a long string of powers of w into a contribution to the
potentials of many cutoffs. -/

@[expose] public section

namespace Finsler.StringBound

open Module
open Finsler.TripleK Finsler.TotalExact Finsler.LadderBudget Finsler.GradedLadder
open Finsler.OperatorK

noncomputable section

variable {G : ℕ → Type} [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
  (wR : ∀ l, G l →ₗ[ZMod 2] G (l + 1))

/-! ### The shift operator and truncation -/

/-- Truncation and the shift operator. -/
theorem cut_shiftOp (j : ℕ) (x : (q : ℕ) → G q) :
    cut G (j + 1) (shiftOp G wR x) = shiftOp G wR (cut G j x) := by
  funext l
  cases l with
  | zero =>
    rw [cut_le (Nat.zero_le _)]
    rfl
  | succ l =>
    rw [shiftOp_succ]
    by_cases h : l ≤ j
    · rw [cut_le (by omega : l + 1 ≤ j + 1), shiftOp_succ, cut_le h]
    · rw [cut_gt (by omega : j + 1 < l + 1), cut_gt (Nat.not_le.mp h), map_zero]

/-- Truncation and powers of the shift operator. -/
theorem cut_shiftOp_pow (j q : ℕ) (x : (q : ℕ) → G q) :
    cut G (j + q) ((shiftOp G wR ^ q) x) = (shiftOp G wR ^ q) (cut G j x) := by
  induction q with
  | zero =>
    rw [pow_zero]
    rfl
  | succ q ih =>
    rw [pow_succ']
    change cut G (j + q + 1) (shiftOp G wR ((shiftOp G wR ^ q) x)) =
      shiftOp G wR ((shiftOp G wR ^ q) (cut G j x))
    rw [cut_shiftOp, ih]

/-- A family vanishing below a has a q-th shift vanishing below a + q. -/
theorem shiftOp_pow_below (q a : ℕ) (x : (q : ℕ) → G q) (hx : ∀ l, l < a → x l = 0) :
    ∀ m, m < a + q → (shiftOp G wR ^ q) x m = 0 := by
  induction q with
  | zero =>
    intro m hm
    rw [pow_zero]
    exact hx m hm
  | succ q ih =>
    intro m hm
    rw [pow_succ']
    change shiftOp G wR ((shiftOp G wR ^ q) x) m = 0
    cases m with
    | zero => rfl
    | succ m =>
      rw [shiftOp_succ, ih m (by omega), map_zero]

/-- A family which vanishes in the degrees at most j is killed by the truncation. -/
theorem cut_eq_zero (j : ℕ) (x : (q : ℕ) → G q) (hx : ∀ l, l ≤ j → x l = 0) :
    cut G j x = 0 := by
  funext l
  by_cases h : l ≤ j
  · rw [cut_le h, hx l h]
    rfl
  · rw [cut_gt (Nat.not_le.mp h)]
    rfl

/-! ### The comparison maps and the two operators -/

section Rules

variable {A : ℕ → Type} [∀ q, AddCommGroup (A q)] [∀ q, Module (ZMod 2) (A q)]
  (e : ∀ q l, A q →ₗ[ZMod 2] G l) (v wK : ∀ q, A q →ₗ[ZMod 2] A (q + 1))
  (hv : ∀ q l x, e (q + 1) l (v q x) = e q l x)
  (hw : ∀ q l x, e (q + 1) (l + 1) (wK q x) = wR l (e q l x))
  (hw0 : ∀ q x, e (q + 1) 0 (wK q x) = 0)

include hv in
theorem tot_word_v (lo k : ℕ) (x : A lo) :
    totMap (fun l => e (lo + k) l)
        (Finsler.Gysin.word (V := fun i => A (lo + i))
          (fun i => (v (lo + i)).toAddMonoidHom) k x) =
      totMap (fun l => e lo l) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih]
    funext l
    exact hv (lo + k) l _

include hw hw0 in
theorem tot_word_w (lo k : ℕ) (x : A lo) :
    totMap (fun l => e (lo + k) l)
        (Finsler.Gysin.word (V := fun i => A (lo + i))
          (fun i => (wK (lo + i)).toAddMonoidHom) k x) =
      (shiftOp G wR ^ k) (totMap (fun l => e lo l) x) := by
  induction k with
  | zero =>
    rw [pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ']
    change _ = shiftOp G wR ((shiftOp G wR ^ k) (totMap (fun l => e lo l) x))
    rw [← ih]
    funext l
    cases l with
    | zero => exact hw0 (lo + k) _
    | succ l => exact hw (lo + k) l _

end Rules

/-! ### Strings -/

section String

variable (y : ∀ l, G l) (L₀ ν : ℕ)

/-- The family with coefficient c_i times y_{L₀ + i} in the degree L₀ + i, i < ν. -/
def strMap : (Fin ν → ZMod 2) →ₗ[ZMod 2] ((q : ℕ) → G q) where
  toFun c l := if h : L₀ ≤ l ∧ l < L₀ + ν then c ⟨l - L₀, by omega⟩ • y l else 0
  map_add' c c' := by
    funext l
    by_cases h : L₀ ≤ l ∧ l < L₀ + ν
    · change (if h : L₀ ≤ l ∧ l < L₀ + ν then (c + c') ⟨l - L₀, by omega⟩ • y l else 0) =
        (if h : L₀ ≤ l ∧ l < L₀ + ν then c ⟨l - L₀, by omega⟩ • y l else 0) +
          (if h : L₀ ≤ l ∧ l < L₀ + ν then c' ⟨l - L₀, by omega⟩ • y l else 0)
      rw [dite_eq_left h, dite_eq_left h, dite_eq_left h, Pi.add_apply, add_smul]
    · change (if h : L₀ ≤ l ∧ l < L₀ + ν then (c + c') ⟨l - L₀, by omega⟩ • y l else 0) =
        (if h : L₀ ≤ l ∧ l < L₀ + ν then c ⟨l - L₀, by omega⟩ • y l else 0) +
          (if h : L₀ ≤ l ∧ l < L₀ + ν then c' ⟨l - L₀, by omega⟩ • y l else 0)
      rw [dite_eq_right h, dite_eq_right h, dite_eq_right h, add_zero]
  map_smul' r c := by
    funext l
    by_cases h : L₀ ≤ l ∧ l < L₀ + ν
    · change (if h : L₀ ≤ l ∧ l < L₀ + ν then (r • c) ⟨l - L₀, by omega⟩ • y l else 0) =
        r • (if h : L₀ ≤ l ∧ l < L₀ + ν then c ⟨l - L₀, by omega⟩ • y l else 0)
      rw [dite_eq_left h, dite_eq_left h, Pi.smul_apply, smul_assoc]
    · change (if h : L₀ ≤ l ∧ l < L₀ + ν then (r • c) ⟨l - L₀, by omega⟩ • y l else 0) =
        r • (if h : L₀ ≤ l ∧ l < L₀ + ν then c ⟨l - L₀, by omega⟩ • y l else 0)
      rw [dite_eq_right h, dite_eq_right h, smul_zero]

theorem strMap_of_mem (c : Fin ν → ZMod 2) {l : ℕ} (h : L₀ ≤ l ∧ l < L₀ + ν) :
    strMap y L₀ ν c l = c ⟨l - L₀, by omega⟩ • y l :=
  dite_eq_left h

theorem strMap_of_not_mem (c : Fin ν → ZMod 2) {l : ℕ} (h : ¬(L₀ ≤ l ∧ l < L₀ + ν)) :
    strMap y L₀ ν c l = 0 :=
  dite_eq_right h

theorem strMap_at (c : Fin ν → ZMod 2) (i : Fin ν) :
    strMap y L₀ ν c (L₀ + i) = c i • y (L₀ + i) := by
  have h : L₀ ≤ L₀ + (i : ℕ) ∧ L₀ + (i : ℕ) < L₀ + ν := ⟨Nat.le_add_right _ _, by omega⟩
  rw [strMap_of_mem y L₀ ν c h]
  congr 2
  apply Fin.ext
  exact Nat.add_sub_cancel_left L₀ (i : ℕ)

/-- The families of the string vanish below L₀. -/
theorem strMap_below (c : Fin ν → ZMod 2) (l : ℕ) (hl : l < L₀) : strMap y L₀ ν c l = 0 :=
  strMap_of_not_mem y L₀ ν c fun h => by omega

/-- The families of the string lie in the root degrees at most j if L₀ + ν ≤ j + 1. -/
theorem range_strMap_le (j : ℕ) (hj : L₀ + ν ≤ j + 1) :
    LinearMap.range (strMap y L₀ ν) ≤ LinearMap.range (cut G j) := by
  rintro _ ⟨c, rfl⟩
  exact (mem_range_cut j _).mpr fun l hl => strMap_of_not_mem y L₀ ν c fun h => by omega

/-- The powers of w along a string. -/
theorem word_string (hy : ∀ l, L₀ ≤ l → wR l (y l) = y (l + 1)) (l q : ℕ) (hl : L₀ ≤ l) :
    Finsler.Gysin.word (V := fun i => G (l + i)) (fun i => (wR (l + i)).toAddMonoidHom) q
      (y l) = y (l + q) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change wR (l + q) (Finsler.Gysin.word (V := fun i => G (l + i))
      (fun i => (wR (l + i)).toAddMonoidHom) q (y l)) = y (l + q + 1)
    rw [ih]
    exact hy (l + q) (by omega)

/-- The q-th shift is injective on the families of a string which is nonzero on
[L₀ + q, L₀ + ν + q). -/
theorem shift_strMap_eq_zero (hy : ∀ l, L₀ ≤ l → wR l (y l) = y (l + 1)) (q : ℕ)
    (hne : ∀ l, L₀ + q ≤ l → l < L₀ + ν + q → y l ≠ 0) (c : Fin ν → ZMod 2)
    (hc : (shiftOp G wR ^ q) (strMap y L₀ ν c) = 0) : c = 0 := by
  funext i
  by_contra hci
  have hci' : c i ≠ 0 := hci
  have hci1 : c i = 1 := by
    have h : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    exact (h (c i)).resolve_left hci'
  have h1 := shiftOp_pow_apply wR q (L₀ + i) (strMap y L₀ ν c)
  rw [hc, strMap_at, hci1, one_smul, word_string wR y L₀ hy (L₀ + i) q (Nat.le_add_right _ _)]
    at h1
  exact hne (L₀ + i + q) (by omega) (by omega) h1.symm

/-- The string starting from a class y₀ of degree g₀: zero below g₀, y₀ in degree g₀, and the
powers of w above. -/
def strFrom (g₀ : ℕ) (y₀ : G g₀) : ∀ l, G l
  | 0 => if h : g₀ = 0 then h ▸ y₀ else 0
  | l + 1 => if h : g₀ = l + 1 then h ▸ y₀ else wR l (strFrom g₀ y₀ l)

theorem strFrom_self (g₀ : ℕ) (y₀ : G g₀) : strFrom wR g₀ y₀ g₀ = y₀ := by
  cases g₀ with
  | zero => exact dite_eq_left rfl
  | succ g => exact dite_eq_left rfl

theorem strFrom_succ (g₀ : ℕ) (y₀ : G g₀) (l : ℕ) (hl : g₀ ≤ l) :
    strFrom wR g₀ y₀ (l + 1) = wR l (strFrom wR g₀ y₀ l) :=
  dite_eq_right (by omega)

end String

/-! ### The inequality -/

section Main

variable {A : ℕ → Type} [∀ q, AddCommGroup (A q)] [∀ q, Module (ZMod 2) (A q)]
  (e : ∀ q l, A q →ₗ[ZMod 2] G l) (v wK : ∀ q, A q →ₗ[ZMod 2] A (q + 1))

/-- A string of length ν against two cutoffs: ν is at most the dimension missing from the
truncated image at the cutoff j in the degree d plus the dimension of the image classes of the
degree d + q + m which vanish in the root degrees at most j'. -/
theorem string_le (hG : FinTot G)
    (hv : ∀ q l x, e (q + 1) l (v q x) = e q l x)
    (hw : ∀ q l x, e (q + 1) (l + 1) (wK q x) = wR l (e q l x))
    (hw0 : ∀ q x, e (q + 1) 0 (wK q x) = 0)
    (y : ∀ l, G l) (L₀ ν q : ℕ) (hy : ∀ l, L₀ ≤ l → wR l (y l) = y (l + 1))
    (hne : ∀ l, L₀ ≤ l → l < L₀ + ν + q → y l ≠ 0)
    (j d m j' : ℕ) (hj : L₀ + ν ≤ j + 1) (hj' : j' < L₀ + q) :
    ν + finrank (ZMod 2) ((LinearMap.range (totMap fun l => e d l)).map (cut G j)) ≤
      finrank (ZMod 2) (LinearMap.range (cut G j)) +
        finrank (ZMod 2) (LinearMap.range (totMap fun l => e (d + q + m) l) ⊓
          LinearMap.ker (cut G j') : Submodule (ZMod 2) ((q : ℕ) → G q)) := by
  have : Module.Finite (ZMod 2) ((q : ℕ) → G q) := hG
  -- the string
  have hinj : Function.Injective (strMap y L₀ ν) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    refine shift_strMap_eq_zero wR y L₀ ν hy 0 (fun l hl hl' => hne l (by omega) (by omega)) c ?_
    rw [pow_zero]
    exact hc
  have h1 : finrank (ZMod 2) (LinearMap.range (strMap y L₀ ν)) = ν := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  -- the intersection with the truncated image
  have hW : LinearMap.range (strMap y L₀ ν) ≤ LinearMap.range (cut G j) :=
    range_strMap_le y L₀ ν j hj
  have hPE : (LinearMap.range (totMap fun l => e d l)).map (cut G j) ≤
      LinearMap.range (cut G j) := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (strMap y L₀ ν))
    ((LinearMap.range (totMap fun l => e d l)).map (cut G j))
  have h3 := Submodule.finrank_mono (sup_le hW hPE)
  -- the shift is injective on the intersection
  have h4 := finrank_eq_inf_ker_add_map (shiftOp G wR ^ q)
    (LinearMap.range (strMap y L₀ ν) ⊓
      (LinearMap.range (totMap fun l => e d l)).map (cut G j))
  have h5 : (LinearMap.range (strMap y L₀ ν) ⊓
      (LinearMap.range (totMap fun l => e d l)).map (cut G j)) ⊓
      LinearMap.ker (shiftOp G wR ^ q) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨⟨c, rfl⟩, -⟩, hk⟩
    have hc0 := shift_strMap_eq_zero wR y L₀ ν hy q
      (fun l hl hl' => hne l (by omega) hl') c (LinearMap.mem_ker.mp hk)
    rw [hc0, map_zero]
    exact Submodule.zero_mem _
  rw [h5, finrank_bot, zero_add] at h4
  -- the shifted intersection lies in the truncation of the classes of the upper degree
  have h6 : (LinearMap.range (strMap y L₀ ν) ⊓
      (LinearMap.range (totMap fun l => e d l)).map (cut G j)).map (shiftOp G wR ^ q) ≤
      (LinearMap.range (totMap fun l => e (d + q + m) l) ⊓
        LinearMap.ker (cut G j') : Submodule (ZMod 2) ((q : ℕ) → G q)).map (cut G (j + q)) := by
    rintro _ ⟨z, ⟨⟨c, hcz⟩, ⟨x, ⟨u, rfl⟩, hxz⟩⟩, rfl⟩
    have hΨ : totMap (fun l => e (d + q + m) l)
        (Finsler.Gysin.word (V := fun i => A (d + q + i))
          (fun i => (v (d + q + i)).toAddMonoidHom) m
          (Finsler.Gysin.word (V := fun i => A (d + i))
            (fun i => (wK (d + i)).toAddMonoidHom) q u)) =
        (shiftOp G wR ^ q) (totMap (fun l => e d l) u) := by
      rw [tot_word_v e v hv (d + q) m, tot_word_w wR e wK hw hw0 d q]
    have hlow : ∀ l, l < L₀ → totMap (fun l => e d l) u l = 0 := by
      intro l hl
      have h7 : cut G j (totMap (fun l => e d l) u) l = z l := congrFun hxz l
      rw [cut_le (by omega : l ≤ j)] at h7
      rw [h7, ← hcz]
      exact strMap_below y L₀ ν c l hl
    refine ⟨(shiftOp G wR ^ q) (totMap (fun l => e d l) u), ⟨⟨_, hΨ⟩, ?_⟩, ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact cut_eq_zero j' _ fun l hl =>
        shiftOp_pow_below wR q L₀ _ hlow l (by omega)
    · rw [cut_shiftOp_pow, hxz]
  have h7 := Submodule.finrank_mono h6
  have h8 := Submodule.finrank_map_le (cut G (j + q))
    (LinearMap.range (totMap fun l => e (d + q + m) l) ⊓
      LinearMap.ker (cut G j') : Submodule (ZMod 2) ((q : ℕ) → G q))
  omega

/-- A string against two cutoffs, in terms of the potentials: ν is at most the sum of the
potentials of the cutoffs k + 1 and k' + 1, if the string of length ν starting at L₀ lies in the
root degrees at most k + 1, the cutoff k' + 1 is below L₀ + q, and 2k + q ≤ 2k'. -/
theorem string_le_gphi (hG : FinTot G) [∀ q, Module.Finite (ZMod 2) (A q)]
    (hv : ∀ q l x, e (q + 1) l (v q x) = e q l x)
    (hw : ∀ q l x, e (q + 1) (l + 1) (wK q x) = wR l (e q l x))
    (hw0 : ∀ q x, e (q + 1) 0 (wK q x) = 0)
    (y : ∀ l, G l) (L₀ ν q : ℕ) (hy : ∀ l, L₀ ≤ l → wR l (y l) = y (l + 1))
    (hne : ∀ l, L₀ ≤ l → l < L₀ + ν + q → y l ≠ 0)
    (k k' : ℕ) (hk : L₀ + ν ≤ k + 1 + 1) (hk' : k' + 1 < L₀ + q) (hkk : 2 * k + q ≤ 2 * k') :
    (ν : ℤ) ≤ gphi G (k + 1) (fun l => e (2 * k + 1 + 1) l) (fun l => e (2 * k + 1) l) +
      gphi G (k' + 1) (fun l => e (2 * k' + 1 + 1) l) (fun l => e (2 * k' + 1) l) := by
  have h := string_le wR e v wK hG hv hw hw0 y L₀ ν q hy hne (k + 1) (2 * k + 1 + 1)
    (2 * k' - 2 * k - q) (k' + 1) hk hk'
  have hdeg : 2 * k + 1 + 1 + q + (2 * k' - 2 * k - q) = 2 * k' + 1 + 1 := by omega
  rw [hdeg] at h
  have h1 := low_defect_le G hG (k + 1) (fun l => e (2 * k + 1 + 1) l)
    (fun l => e (2 * k + 1) l)
  have h2 := high_image_le G hG (k' + 1) (fun l => e (2 * k' + 1 + 1) l)
    (fun l => e (2 * k' + 1) l)
  omega

/-- A long string against a budget for the potentials. If the sums of the potentials of the
cutoffs, given as numbers Φ_k, are at most B, a string of length ν starting at L₀ which is nonzero up to L₀ + ν + q, a
block of N₁ cutoffs above the string and a block of N₂ cutoffs below L₀ + q with enough room
between the degrees satisfy N₁ · N₂ · ν ≤ (N₁ + N₂) · B. -/
theorem string_budget (hG : FinTot G) [∀ q, Module.Finite (ZMod 2) (A q)]
    (hv : ∀ q l x, e (q + 1) l (v q x) = e q l x)
    (hw : ∀ q l x, e (q + 1) (l + 1) (wK q x) = wR l (e q l x))
    (hw0 : ∀ q x, e (q + 1) 0 (wK q x) = 0)
    (Φ : ℕ → ℤ) (hΦ : ∀ k, Φ k =
      gphi G (k + 1) (fun l => e (2 * k + 1 + 1) l) (fun l => e (2 * k + 1) l))
    (B : ℤ) (hBΦ : ∀ K : ℕ, ∑ k ∈ Finset.range K, Φ k ≤ B)
    (y : ∀ l, G l) (L₀ ν q : ℕ) (hy : ∀ l, L₀ ≤ l → wR l (y l) = y (l + 1))
    (hne : ∀ l, L₀ ≤ l → l < L₀ + ν + q → y l ≠ 0)
    (k₁ N₁ k₂ N₂ : ℕ) (h₁ : L₀ + ν ≤ k₁ + 1 + 1) (h₂ : k₂ + N₂ < L₀ + q)
    (h₁₂ : 2 * (k₁ + N₁) + q ≤ 2 * k₂ + 2) :
    (N₁ : ℤ) * (N₂ : ℤ) * (ν : ℤ) ≤ ((N₁ : ℤ) + (N₂ : ℤ)) * B := by
  have hB : ∀ K : ℕ, ∑ k ∈ Finset.range K,
      gphi G (k + 1) (fun l => e (2 * k + 1 + 1) l) (fun l => e (2 * k + 1) l) ≤ B :=
    fun K => (Finset.sum_congr rfl fun k _ => (hΦ k).symm).trans_le (hBΦ K)
  have hnn : ∀ k, 0 ≤ gphi G (k + 1) (fun l => e (2 * k + 1 + 1) l)
      (fun l => e (2 * k + 1) l) := fun k => gphi_nonneg G hG (k + 1) _ _
  -- a block of consecutive cutoffs is bounded by the budget
  have hblock : ∀ k₀ N : ℕ, ∑ i ∈ Finset.range N,
      gphi G (k₀ + i + 1) (fun l => e (2 * (k₀ + i) + 1 + 1) l)
        (fun l => e (2 * (k₀ + i) + 1) l) ≤ B := by
    intro k₀ N
    have h := hB (k₀ + N)
    rw [Finset.sum_range_add] at h
    have h0 : 0 ≤ ∑ k ∈ Finset.range k₀,
        gphi G (k + 1) (fun l => e (2 * k + 1 + 1) l) (fun l => e (2 * k + 1) l) :=
      Finset.sum_nonneg fun k _ => hnn k
    linarith
  have hpair : ∀ i ∈ Finset.range N₁, ∀ i' ∈ Finset.range N₂, (ν : ℤ) ≤
      gphi G (k₁ + i + 1) (fun l => e (2 * (k₁ + i) + 1 + 1) l)
          (fun l => e (2 * (k₁ + i) + 1) l) +
        gphi G (k₂ + i' + 1) (fun l => e (2 * (k₂ + i') + 1 + 1) l)
          (fun l => e (2 * (k₂ + i') + 1) l) := by
    intro i hi i' hi'
    have hi1 := Finset.mem_range.mp hi
    have hi2 := Finset.mem_range.mp hi'
    exact string_le_gphi wR e v wK hG hv hw hw0 y L₀ ν q hy hne (k₁ + i) (k₂ + i')
      (by omega) (by omega) (by omega)
  have hsum : ∑ i ∈ Finset.range N₁, ∑ i' ∈ Finset.range N₂, (ν : ℤ) ≤
      ∑ i ∈ Finset.range N₁, ∑ i' ∈ Finset.range N₂,
        (gphi G (k₁ + i + 1) (fun l => e (2 * (k₁ + i) + 1 + 1) l)
            (fun l => e (2 * (k₁ + i) + 1) l) +
          gphi G (k₂ + i' + 1) (fun l => e (2 * (k₂ + i') + 1 + 1) l)
            (fun l => e (2 * (k₂ + i') + 1) l)) :=
    Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun i' hi' => hpair i hi i' hi'
  have hl : ∑ i ∈ Finset.range N₁, ∑ i' ∈ Finset.range N₂, (ν : ℤ) =
      (N₁ : ℤ) * (N₂ : ℤ) * (ν : ℤ) := by
    rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
    ring
  have hr : ∑ i ∈ Finset.range N₁, ∑ i' ∈ Finset.range N₂,
        (gphi G (k₁ + i + 1) (fun l => e (2 * (k₁ + i) + 1 + 1) l)
            (fun l => e (2 * (k₁ + i) + 1) l) +
          gphi G (k₂ + i' + 1) (fun l => e (2 * (k₂ + i') + 1 + 1) l)
            (fun l => e (2 * (k₂ + i') + 1) l)) =
      (N₂ : ℤ) * ∑ i ∈ Finset.range N₁,
          gphi G (k₁ + i + 1) (fun l => e (2 * (k₁ + i) + 1 + 1) l)
            (fun l => e (2 * (k₁ + i) + 1) l) +
        (N₁ : ℤ) * ∑ i' ∈ Finset.range N₂,
          gphi G (k₂ + i' + 1) (fun l => e (2 * (k₂ + i') + 1 + 1) l)
            (fun l => e (2 * (k₂ + i') + 1) l) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hl, hr] at hsum
  have hb1 := hblock k₁ N₁
  have hb2 := hblock k₂ N₂
  have hN₁ : (0 : ℤ) ≤ N₁ := Nat.cast_nonneg N₁
  have hN₂ : (0 : ℤ) ≤ N₂ := Nat.cast_nonneg N₂
  nlinarith [mul_le_mul_of_nonneg_left hb1 hN₂, mul_le_mul_of_nonneg_left hb2 hN₁]

end Main

end

end Finsler.StringBound
