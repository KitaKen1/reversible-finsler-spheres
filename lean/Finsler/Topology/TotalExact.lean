module

public import Finsler.Topology.TripleK

/-! Totals of graded exact sequences. For graded F₂-vector spaces G', G, G'' and degreewise maps
i : G' → G, p : G → G'' of degree zero and d : G'' → G' of degree one forming a long exact
sequence, the maps induced on the products over all degrees form an exact sequence
ΠG' → ΠG → ΠG'' → ΠG' → ΠG. The truncation to the degrees at most j is an idempotent of each
product which commutes with the maps of degree zero, and with the map of degree one if d
vanishes on the degree j. If every piece is finite dimensional and the pieces vanish from some
degree on, the product is finite dimensional. -/

@[expose] public section

namespace Finsler.TotalExact

open Finsler.TripleK

noncomputable section

section

variable {G' G G'' : ℕ → Type} [∀ q, AddCommGroup (G' q)] [∀ q, Module (ZMod 2) (G' q)]
  [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
  [∀ q, AddCommGroup (G'' q)] [∀ q, Module (ZMod 2) (G'' q)]

theorem piMap_apply (i : ∀ q, G' q →ₗ[ZMod 2] G q) (x : (q : ℕ) → G' q) (q : ℕ) :
    piMap i x q = i q (x q) := rfl

theorem shiftMap_zero (d : ∀ q, G'' q →ₗ[ZMod 2] G' (q + 1)) (x : (q : ℕ) → G'' q) :
    shiftMap d x 0 = 0 := rfl

theorem shiftMap_succ (d : ∀ q, G'' q →ₗ[ZMod 2] G' (q + 1)) (x : (q : ℕ) → G'' q) (q : ℕ) :
    shiftMap d x (q + 1) = d q (x q) := rfl

/-! ### Exactness of the totals -/

/-- Exactness at the middle term of two maps of degree zero. -/
theorem ker_piMap (i : ∀ q, G' q →ₗ[ZMod 2] G q) (p : ∀ q, G q →ₗ[ZMod 2] G'' q)
    (hzero : ∀ q y, p q (i q y) = 0) (hex : ∀ q x, p q x = 0 → ∃ y, i q y = x) :
    LinearMap.ker (piMap p) = LinearMap.range (piMap i) := by
  ext x
  constructor
  · intro hx
    have h : ∀ q, ∃ y, i q y = x q := fun q =>
      hex q (x q) (congrFun (LinearMap.mem_ker.mp hx) q)
    choose y hy using h
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext q
    exact hzero q (y q)

/-- Exactness at the source of the map of degree one. -/
theorem ker_shiftMap (p : ∀ q, G q →ₗ[ZMod 2] G'' q) (d : ∀ q, G'' q →ₗ[ZMod 2] G' (q + 1))
    (hzero : ∀ q y, d q (p q y) = 0) (hex : ∀ q x, d q x = 0 → ∃ y, p q y = x) :
    LinearMap.ker (shiftMap d) = LinearMap.range (piMap p) := by
  ext x
  constructor
  · intro hx
    have h : ∀ q, ∃ y, p q y = x q := fun q =>
      hex q (x q) (congrFun (LinearMap.mem_ker.mp hx) (q + 1))
    choose y hy using h
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext q
    cases q with
    | zero => rfl
    | succ q => exact hzero q (y q)

/-- Exactness at the target of the map of degree one. -/
theorem ker_piMap_shift (d : ∀ q, G'' q →ₗ[ZMod 2] G' (q + 1)) (i : ∀ q, G' q →ₗ[ZMod 2] G q)
    (hinj : Function.Injective (i 0)) (hzero : ∀ q x, i (q + 1) (d q x) = 0)
    (hex : ∀ q y, i (q + 1) y = 0 → ∃ x, d q x = y) :
    LinearMap.ker (piMap i) = LinearMap.range (shiftMap d) := by
  ext y
  constructor
  · intro hy
    have hy' : ∀ q, i q (y q) = 0 := fun q => congrFun (LinearMap.mem_ker.mp hy) q
    have h : ∀ q, ∃ x, d q x = y (q + 1) := fun q => hex q (y (q + 1)) (hy' (q + 1))
    choose x hx using h
    refine ⟨x, ?_⟩
    funext q
    cases q with
    | zero => exact (hinj ((hy' 0).trans (map_zero (i 0)).symm)).symm
    | succ q => exact hx q
  · rintro ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext q
    cases q with
    | zero => exact map_zero (i 0)
    | succ q => exact hzero q (x q)

end

/-! ### Truncation -/

section Cut

variable (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]

/-- Truncation of a family to the degrees at most j. -/
def cut (j : ℕ) : ((q : ℕ) → G q) →ₗ[ZMod 2] ((q : ℕ) → G q) where
  toFun x q := if q ≤ j then x q else 0
  map_add' x y := by
    funext q
    by_cases h : q ≤ j
    · change (if q ≤ j then (x + y) q else 0) =
        (if q ≤ j then x q else 0) + (if q ≤ j then y q else 0)
      rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      rfl
    · change (if q ≤ j then (x + y) q else 0) =
        (if q ≤ j then x q else 0) + (if q ≤ j then y q else 0)
      rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, add_zero]
  map_smul' c x := by
    funext q
    by_cases h : q ≤ j
    · change (if q ≤ j then (c • x) q else 0) = c • (if q ≤ j then x q else 0)
      rw [ite_eq_left h, ite_eq_left h]
      rfl
    · change (if q ≤ j then (c • x) q else 0) = c • (if q ≤ j then x q else 0)
      rw [ite_eq_right h, ite_eq_right h, smul_zero]

variable {G}

theorem cut_le {j q : ℕ} (h : q ≤ j) (x : (q : ℕ) → G q) : cut G j x q = x q :=
  ite_eq_left h

theorem cut_gt {j q : ℕ} (h : j < q) (x : (q : ℕ) → G q) : cut G j x q = 0 :=
  ite_eq_right (Nat.not_le.mpr h)

theorem cut_cut (j : ℕ) (x : (q : ℕ) → G q) : cut G j (cut G j x) = cut G j x := by
  funext q
  by_cases h : q ≤ j
  · rw [cut_le h, cut_le h]
  · rw [cut_gt (Nat.not_le.mp h), cut_gt (Nat.not_le.mp h)]

/-- A family lies in the image of the truncation if and only if it vanishes above j. -/
theorem mem_range_cut (j : ℕ) (x : (q : ℕ) → G q) :
    x ∈ LinearMap.range (cut G j) ↔ ∀ q, j < q → x q = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ q hq
    exact cut_gt hq y
  · intro hx
    refine ⟨x, ?_⟩
    funext q
    by_cases h : q ≤ j
    · exact cut_le h x
    · rw [cut_gt (Nat.not_le.mp h), hx q (Nat.not_le.mp h)]

variable {G' G'' : ℕ → Type} [∀ q, AddCommGroup (G' q)] [∀ q, Module (ZMod 2) (G' q)]
  [∀ q, AddCommGroup (G'' q)] [∀ q, Module (ZMod 2) (G'' q)]

/-- Truncation commutes with maps of degree zero. -/
theorem piMap_cut (i : ∀ q, G' q →ₗ[ZMod 2] G q) (j : ℕ) (x : (q : ℕ) → G' q) :
    piMap i (cut G' j x) = cut G j (piMap i x) := by
  funext q
  by_cases h : q ≤ j
  · rw [piMap_apply, cut_le h, cut_le h, piMap_apply]
  · rw [piMap_apply, cut_gt (Nat.not_le.mp h), cut_gt (Nat.not_le.mp h), map_zero]

/-- Truncation commutes with a map of degree one which vanishes on the degree j. -/
theorem shiftMap_cut (d : ∀ q, G'' q →ₗ[ZMod 2] G' (q + 1)) (j : ℕ) (hd : ∀ x, d j x = 0)
    (x : (q : ℕ) → G'' q) : shiftMap d (cut G'' j x) = cut G' j (shiftMap d x) := by
  funext q
  cases q with
  | zero => rw [shiftMap_zero, cut_le (Nat.zero_le j), shiftMap_zero]
  | succ q =>
    rw [shiftMap_succ]
    by_cases h : q + 1 ≤ j
    · rw [cut_le (by omega : q ≤ j), cut_le h, shiftMap_succ]
    · rw [cut_gt (Nat.not_le.mp h)]
      by_cases h' : q ≤ j
      · have e : q = j := by omega
        subst e
        exact hd _
      · rw [cut_gt (Nat.not_le.mp h'), map_zero]

end Cut

/-! ### Finite dimensionality -/

/-- A product of finite dimensional pieces which vanish from some degree on is finite
dimensional. -/
theorem finite_total (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
    [∀ q, Module.Finite (ZMod 2) (G q)] {Q : ℕ} (hz : ∀ q, Q ≤ q → ∀ x : G q, x = 0) :
    Module.Finite (ZMod 2) ((q : ℕ) → G q) := by
  have hr : Function.Injective
      (LinearMap.pi (fun q : Fin Q => (LinearMap.proj (q : ℕ) :
        ((q : ℕ) → G q) →ₗ[ZMod 2] G q))) := by
    intro x y hxy
    funext q
    by_cases hq : q < Q
    · exact congrFun hxy ⟨q, hq⟩
    · rw [hz q (by omega) (x q), hz q (by omega) (y q)]
  exact Module.Finite.of_injective _ hr

end

end Finsler.TotalExact
