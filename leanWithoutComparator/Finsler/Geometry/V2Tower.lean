module

public import Finsler.Geometry.RoundV2Dims
public import Finsler.Topology.InvCover
public import Finsler.Topology.LevelBounds

/-! The connecting map of (V₂, A) vanishes (mod 2 Euler class of the round sphere).

Let A ⊆ V₂ be the complement of the fibre over e₀. The long exact sequence of (V₂, A, ∅) reads
H^{n−1}(A) = F₂ → Hⁿ(V₂, A) = F₂ → Hⁿ(V₂) → Hⁿ(A) = 0, so if the connecting map were nonzero,
V₂ would have no cohomology in the degrees n − 1 and n, hence none in 1, …, 2n − 2. The free
involution (x, u) ↦ (x, −u) of V₂ is oriented on the n + 1 sets {u_i ≠ 0}, which cover V₂, so
w^{n+1} = 0 on its reflection Borel cohomology (`InvCover`). In the Gysin sequence a nonzero class
of degree 0 then has a w-tower which is injective up to degree 2n − 1 > n: a contradiction.
Hence the connecting map vanishes, and Hⁿ(V₂, A) → Hⁿ(V₂) is injective. No Euler class, no
clutching function and no projective bundle formula are used. -/

@[expose] public section

namespace Finsler.V2Tower

open CategoryTheory Finsler.SphereGeometry Finsler.RoundChart Finsler.RoundThom
open Finsler.RoundV2Chart Finsler.RoundV2Dims Finsler.TrivHq Finsler.InvCover
open Finsler.BorelCochain Finsler.BorelPair Finsler.PairTriple Finsler.BorelLoop
open Finsler.BorelExact Finsler.NilpotentW Finsler.BorelCrossing
open Set Module

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### The ordinary long exact sequence -/

section Exact

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

/-- A connecting image becomes zero in the middle complex. -/
theorem Hmap_delta (q : ℕ) (y : H K'' q) : Hmap ι (q + 1) (OrdinaryDelta.delta h q y) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [OrdinaryDelta.delta, Submodule.mapQ_apply, Hmap, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change ι.f (q + 1) (ret h (q + 1) (K.d q (sec h q (c : K''.C q)))) ∈ coboundaries K (q + 1)
  rw [OrdinaryDelta.incl_ret_d_sec h q _ c.2]
  exact ⟨sec h q (c : K''.C q), rfl⟩

/-- The connecting map vanishes on images of the middle complex. -/
theorem delta_Hmap (q : ℕ) (x : H K q) : OrdinaryDelta.delta h q (Hmap π q x) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Hmap, Submodule.mapQ_apply, OrdinaryDelta.delta, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change ret h (q + 1) (K.d q (sec h q (π.f q (c : K.C q)))) ∈ coboundaries K' (q + 1)
  obtain ⟨v, hv⟩ := OrdinaryDelta.d_sec_eq h q (π.f q (c : K.C q)) (c : K.C q) rfl
  have hc : K.d q (c : K.C q) = 0 := c.2
  rw [hv, hc, zero_add, ret_incl]
  exact ⟨v, rfl⟩

end Exact

/-- Two nonzero vectors of a space of dimension at most one over F₂ are equal. -/
theorem eq_of_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (hV : finrank (ZMod 2) V ≤ 1) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hV
  obtain ⟨c, rfl⟩ := hv x
  obtain ⟨c', rfl⟩ := hv y
  have h2 : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  rcases h2 c with rfl | rfl
  · exact absurd (zero_smul _ v) hx
  rcases h2 c' with rfl | rfl
  · exact absurd (zero_smul _ v) hy
  rfl

/-! ### Towers of w -/

/-- **Tower contradiction.** If w^N vanishes in degree zero, the ordinary cohomology is
one-dimensional in degree zero and vanishes in the degrees 1, …, M with N ≤ M + 1, then there is
a contradiction. -/
theorem tower_false (K : InvComplex) {N M : ℕ} (hNM : N ≤ M + 1)
    (hw : ∀ x : HR K 0, wPow K 0 N x = 0) (z₀ : H K 0) (hz₀ : z₀ ≠ 0)
    (h0 : ∀ z : H K 0, z = 0 ∨ z = z₀) (hq : ∀ q, 1 ≤ q → q ≤ M → ∀ z : H K q, z = 0) :
    False := by
  -- the transfer vanishes in degree zero
  have htr00 : transfer K 0 z₀ = 0 := by
    by_contra hne
    rcases h0 (BorelCochain.forget K 0 (transfer K 0 z₀)) with hf | hf
    · exact hne (Finsler.BorelQuasiIso.forget_zero_injective K (hf.trans (map_zero _).symm))
    · apply hne
      rw [← hf]
      exact (exact_transfer K 0 _).mpr ⟨_, rfl⟩
  have htr0 : ∀ z : H K 0, transfer K 0 z = 0 := by
    intro z
    rcases h0 z with h | h
    · rw [h, map_zero]
    · rw [h]
      exact htr00
  -- w is injective up to degree M
  have hinj : ∀ q, q ≤ M → ∀ y : HR K q, w K q y = 0 → y = 0 := by
    intro q hqM y hy
    obtain ⟨z, rfl⟩ := (exact_w K q y).mp hy
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · exact htr0 z
    · rw [hq q hpos hqM z, map_zero]
  -- a nonzero class of degree zero
  obtain ⟨x₀, hx₀⟩ := (exact_transfer K 0 z₀).mp (htr0 z₀)
  have hx₀0 : x₀ ≠ 0 := fun h => hz₀ (by rw [← hx₀, h, map_zero])
  have key : ∀ k, k ≤ M + 1 → wPow K 0 k x₀ ≠ 0 := by
    intro k
    induction k with
    | zero => exact fun _ => hx₀0
    | succ k ih =>
      intro hk h
      rw [wPow_succ] at h
      exact ih (by omega) (hinj (0 + k) (by omega) _ h)
  exact key N hNM (hw x₀)

/-! ### The involution of V₂ -/

/-- The involution (x, u) ↦ (x, −u) of V₂. -/
def flipU (n : ℕ) : C(V2T n, V2T n) :=
  ⟨fun z => ⟨(z.1.1, -z.1.2), z.2.1, by rw [norm_neg]; exact z.2.2.1,
      by rw [inner_neg_right, z.2.2.2, neg_zero]⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_snd.comp continuous_subtype_val).neg).subtype_mk _⟩

theorem flipU_flipU (z : V2T n) : flipU n (flipU n z) = z :=
  Subtype.ext (Prod.ext rfl (neg_neg _))

/-- A coordinate of the second vector. -/
def coordU (i : Fin (n + 1)) (z : V2T n) : ℝ := (z.1.2 : Ambient n) i

theorem coordU_continuous (i : Fin (n + 1)) : Continuous (coordU (n := n) i) :=
  (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp
    (continuous_snd.comp continuous_subtype_val))

theorem coordU_flip (i : Fin (n + 1)) (z : V2T n) : coordU i (flipU n z) = -coordU i z := by
  change ((-(z.1.2 : Ambient n) : Ambient n)) i = -((z.1.2 : Ambient n) i)
  simp

/-- The oriented set {u_i ≠ 0}. -/
def orientedU (i : Fin (n + 1)) : Oriented (flipU n) where
  V := {z | coordU i z ≠ 0}
  isOpen := isOpen_ne_fun (coordU_continuous i) continuous_const
  inv := fun z hz => by
    change coordU i (flipU n z) ≠ 0
    rw [coordU_flip]
    exact neg_ne_zero.mpr hz
  orient :=
    { pos := {z | 0 < coordU i z}
      neg := {z | coordU i z < 0}
      pos_open := isOpen_lt continuous_const (coordU_continuous i)
      neg_open := isOpen_lt (coordU_continuous i) continuous_const
      cover := fun z hz => (lt_or_gt_of_ne hz).elim (fun h => Or.inr h) (fun h => Or.inl h)
      disjoint := fun z _ h1 h2 => lt_irrefl _ (lt_trans (show coordU i z < 0 from h2)
        (show 0 < coordU i z from h1))
      swap_pos := fun z hz => by
        change coordU i (flipU n z) < 0
        rw [coordU_flip]
        exact neg_neg_of_pos hz
      swap_neg := fun z hz => by
        change 0 < coordU i (flipU n z)
        rw [coordU_flip]
        exact neg_pos.mpr hz }

/-- The list of the n + 1 oriented sets. -/
def orientedList (n : ℕ) : List (Oriented (flipU n)) := List.ofFn fun i : Fin (n + 1) => orientedU i

theorem mem_unionOf {ι : C(V2T n, V2T n)} (N : Set (V2T n)) (l : List (Oriented ι)) (z : V2T n) :
    z ∈ unionOf N l ↔ z ∈ N ∨ ∃ T ∈ l, z ∈ T.V := by
  induction l with
  | nil => simp [unionOf]
  | cons T l ih =>
    change z ∈ unionOf N l ∪ T.V ↔ _
    rw [mem_union, ih]
    constructor
    · rintro ((h | ⟨T', hT', hz⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨T', List.mem_cons_of_mem T hT', hz⟩
      · exact Or.inr ⟨T, List.mem_cons_self, h⟩
    · rintro (h | ⟨T', hT', hz⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hT' with rfl | hT'
        · exact Or.inr hz
        · exact Or.inl (Or.inr ⟨T', hT', hz⟩)

theorem cover_univ : (univ : Set (V2T n)) ⊆ unionOf (univ ∩ ∅) (orientedList n) := by
  intro z _
  rw [mem_unionOf]
  right
  by_contra hno
  have hzero : (z.1.2 : Ambient n) = 0 := by
    ext i
    have h0 : coordU i z = 0 := by
      by_contra hi
      exact hno ⟨orientedU i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
    simpa [coordU] using h0
  have h1 := z.2.2.1
  rw [hzero, norm_zero] at h1
  exact zero_ne_one h1

theorem hN_inv : Inv (flipU n) ((univ : Set (V2T n)) ∩ ∅) := fun _ h => h

theorem hX_inv : Inv (flipU n) (univ : Set (V2T n)) := fun _ _ => mem_univ _

/-- The reflection Borel complex of V₂ for the involution (x, u) ↦ (x, −u). -/
abbrev KV (n : ℕ) : InvComplex :=
  iC flipU_flipU (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) hN_inv hX_inv

/-- **w^{n+1} = 0** on the reflection Borel cohomology of V₂. -/
theorem wPow_V (q : ℕ) (x : HR (KV n) q) : wPow (KV n) q (n + 1) x = 0 := by
  have h := wPow_of_cover flipU_flipU (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ)
    hN_inv hX_inv (isOpen_univ.inter isOpen_empty) (orientedList n) cover_univ (subset_univ _) q x
  rwa [orientedList, List.length_ofFn] at h

/-- The ordinary cohomology of the reflection Borel complex is that of V₂. -/
def kvEquiv (q : ℕ) : H (KV n) q ≃ₗ[ZMod 2] HV n q :=
  Finsler.LevelBounds.ofPairEquiv (emptyPair (V2T n)) _ (Category.comp_id _) q

/-! ### The connecting map -/

theorem A_eq_zero (hn : 2 ≤ n) (k : ℕ) (h0 : k ≠ 0) (h1 : k ≠ n - 1)
    (x : H (triv (pairOf (hst (n := n)))) k) : x = 0 := by
  haveI := A_finite hn k
  have h := A_finrank hn k
  rw [if_neg (by omega)] at h
  have : Subsingleton (H (triv (pairOf (hst (n := n)))) k) := Module.finrank_zero_iff.mp h
  exact Subsingleton.elim _ _

theorem A_le_one (hn : 2 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (H (triv (pairOf (hst (n := n)))) k) ≤ 1 := by
  rw [A_finrank hn k]
  split_ifs <;> omega

theorem P_le_one (hn : 2 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (H (triv (pairOf (subset_univ (AP (n := n))))) k) ≤ 1 := by
  rw [P_finrank hn k]
  split_ifs <;> omega

/-- **The connecting map H^{n−1}(A) → Hⁿ(V₂, A) vanishes.** -/
theorem delta_zero (hn : 2 ≤ n) (q : ℕ) (hq : q + 1 = n) (y : H (triv (pairOf (hst (n := n)))) q) :
    tripleDelta (hst (n := n)) (subset_univ AP) q y = 0 := by
  by_contra hy
  have hse := tripleExact (hst (n := n)) (subset_univ (AP (n := n)))
  have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero])
  -- no cohomology in degree n
  have hVn : ∀ x : HV n (q + 1), x = 0 := by
    intro x
    have hi := A_eq_zero hn (q + 1) (by omega) (by omega)
      (Hmap (trivHom (incPair (hst (n := n)) (subset_univ (AP (n := n))))) (q + 1) x)
    obtain ⟨z, rfl⟩ := exact_mid_ordinary hse (q + 1) x hi
    haveI := P_finite hn (q + 1)
    by_cases hz : z = 0
    · rw [hz, map_zero]
    · have he := eq_of_ne_zero (P_le_one hn (q + 1)) hz hy
      rw [he]
      exact Hmap_delta hse q y
  -- no cohomology in degree n − 1
  have hVq : ∀ x : HV n q, x = 0 := by
    intro x
    have hix : Hmap (trivHom (incPair (hst (n := n)) (subset_univ (AP (n := n))))) q x = 0 := by
      by_contra hne
      haveI := A_finite hn q
      have he := eq_of_ne_zero (A_le_one hn q) hne hy0
      apply hy
      rw [← he]
      exact delta_Hmap hse q x
    obtain ⟨z, rfl⟩ := exact_mid_ordinary hse q x hix
    rw [pair_eq_zero q (by omega) z, map_zero]
  -- no cohomology in the degrees 1, …, 2n − 2
  have hV : ∀ k, 1 ≤ k → k ≤ 2 * n - 2 → ∀ x : HV n k, x = 0 := by
    intro k hk1 hk2 x
    by_cases hkq : k = q
    · subst hkq
      exact hVq x
    by_cases hkn : k = q + 1
    · subst hkn
      exact hVn x
    exact V2_eq_zero (by omega) k (by omega) (by omega) (by omega) (by omega) x
  -- the tower contradiction
  haveI := Finsler.RoundV2Finite.V2_finite (n := n) 0
  have hpos := V2_H0_pos (by omega : 2 ≤ n)
  obtain ⟨z₀, hz₀⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := HV n 0)).mp hpos
  refine tower_false (KV n) (N := n + 1) (M := 2 * n - 2) (by omega) (fun x => wPow_V 0 x)
    ((kvEquiv 0).symm z₀) (fun h => hz₀ (by
      rw [← (kvEquiv 0).apply_symm_apply z₀, h, LinearEquiv.map_zero])) (fun z => ?_)
    (fun k hk1 hk2 z => (kvEquiv k).injective ((hV k hk1 hk2 _).trans
      (LinearEquiv.map_zero _).symm))
  by_cases hz : z = 0
  · exact Or.inl hz
  · right
    apply (kvEquiv 0).injective
    rw [LinearEquiv.apply_symm_apply]
    exact eq_of_ne_zero (V2_finrank_le_one (by omega) 0)
      (fun h => hz ((kvEquiv 0).injective (h.trans (LinearEquiv.map_zero _).symm))) hz₀

/-- **Hⁿ(V₂, A) → Hⁿ(V₂) is injective.** -/
theorem j_injective (hn : 2 ≤ n) (q : ℕ) (hq : q + 1 = n) :
    Function.Injective (Hmap (trivHom (relPair (hst (n := n)) (subset_univ (AP (n := n)))))
      (q + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := OrdinaryDelta.exact_sub (tripleExact (hst (n := n)) (subset_univ AP)) q z hz
  exact delta_zero hn q hq y

end

end Finsler.V2Tower
