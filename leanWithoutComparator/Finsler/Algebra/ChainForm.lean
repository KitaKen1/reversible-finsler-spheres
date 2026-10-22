module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.Data.ZMod.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
public import Finsler.Algebra.AlmostAdditive

/-! The negative index of inertia of the chain forms of the iterates of a closed chain. A family
of pair forms β_j on V × V, indexed by the residues modulo N, defines on the families indexed
by the residues modulo m N the chain form w ↦ Σ_j β_j(w_j, w_{j+1}) of the m-fold iterated
chain. Its negative index of inertia I(m) is additive up to the dimension of V:
|I(m + k) - I(m) - I(k)| ≤ dim V. The proof is the codimension argument: on the families of the
chain of m + k periods whose member at the index m N equals the member at 0, the chain form is
the sum of the chain forms of the two parts; this constraint and the corresponding constraint
on pairs of families (equal members at 0) have codimension at most dim V; restriction to a
subspace of codimension r lowers the negative index by at most r. Hence there is a mean Δ ≥ 0
with |I(m) - m Δ| ≤ dim V for all m ≥ 1. This is the linear algebra of the index of the
iterates of a closed geodesic (elementary form of Bott's iteration estimate). -/

@[expose] public section

namespace Finsler.ChainForm

open Module QuadraticMap

noncomputable section

/-! ### Two comparison lemmas for the negative index of inertia -/

section Index

variable {M M' V' : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  [AddCommGroup M'] [Module ℝ M'] [FiniteDimensional ℝ M']
  [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']

/-- An injective linear map which preserves the forms does not decrease the negative index of
inertia. -/
theorem sigNeg_le_of_injective (Q : QuadraticForm ℝ M) (Q' : QuadraticForm ℝ M')
    (f : M →ₗ[ℝ] M') (hf : Function.Injective f) (h : ∀ x, Q' (f x) = Q x) :
    sigNeg Q ≤ sigNeg Q' := by
  obtain ⟨U, hU, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  rw [← hU, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf U)]
  apply le_sigNeg_of_negDef Q' (V := U.map f)
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ hx0
  have hx' : (⟨x, hx⟩ : U) ≠ 0 := fun h0 => hx0 (by
    apply Subtype.ext
    have hx00 : x = 0 := congrArg Subtype.val h0
    change f x = 0
    rw [hx00, map_zero])
  have hpos := hneg ⟨x, hx⟩ hx'
  rw [restrict_apply, neg_apply] at hpos
  rw [restrict_apply, neg_apply, h]
  exact hpos

/-- Restriction to the kernel of a linear map lowers the negative index of inertia at most by
the dimension of the target. -/
theorem sigNeg_le_restrict_ker_add (Q : QuadraticForm ℝ M) (c : M →ₗ[ℝ] V') :
    sigNeg Q ≤ sigNeg (Q.restrict (LinearMap.ker c)) + finrank ℝ V' := by
  obtain ⟨U, hU, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  set U' : Submodule ℝ (LinearMap.ker c) := U.comap (LinearMap.ker c).subtype with hU'
  have h1 : finrank ℝ U' ≤ sigNeg (Q.restrict (LinearMap.ker c)) := by
    apply le_sigNeg_of_negDef (Q.restrict (LinearMap.ker c)) (V := U')
    rintro ⟨x, hx⟩ hx0
    have hxU : (x : M) ∈ U := hx
    have hx' : (⟨(x : M), hxU⟩ : U) ≠ 0 := fun h0 => hx0 (by
      have hx00 : (x : M) = 0 := congrArg Subtype.val h0
      apply Subtype.ext
      apply Subtype.ext
      exact hx00)
    have hpos := hneg ⟨(x : M), hxU⟩ hx'
    rw [restrict_apply, neg_apply] at hpos
    rw [restrict_apply, neg_apply, restrict_apply]
    exact hpos
  have h2 : finrank ℝ U ≤ finrank ℝ U' + finrank ℝ V' := by
    have e1 : finrank ℝ U' = finrank ℝ (LinearMap.ker c ⊓ U : Submodule ℝ M) := by
      rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker c) U
    have e3 := LinearMap.finrank_range_add_finrank_ker c
    have e4 : finrank ℝ (LinearMap.ker c ⊔ U : Submodule ℝ M) ≤ finrank ℝ M :=
      Submodule.finrank_le _
    have e5 : finrank ℝ (LinearMap.range c) ≤ finrank ℝ V' := Submodule.finrank_le _
    omega
  omega

end Index

/-! ### Chain forms -/

section Def

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {K : ℕ} [NeZero K]

/-- A sum over the residues as a sum over a range. -/
theorem sum_zmod {M : Type*} [AddCommMonoid M] (g : ZMod K → M) :
    ∑ i : ZMod K, g i = ∑ t ∈ Finset.range K, g (t : ZMod K) := by
  refine Finset.sum_bij' (fun a _ => a.val) (fun t _ => (t : ZMod K)) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro t _
    exact Finset.mem_univ _
  · intro a _
    exact ZMod.natCast_zmod_val a
  · intro t ht
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ht)
  · intro a _
    rw [ZMod.natCast_zmod_val]

/-- The two consecutive members of a family at the index j. -/
def edge (j : ZMod K) : (ZMod K → V) →ₗ[ℝ] V × V :=
  (LinearMap.proj j).prod (LinearMap.proj (j + 1))

omit [NeZero K] in
theorem edge_apply (j : ZMod K) (w : ZMod K → V) : edge j w = (w j, w (j + 1)) := rfl

/-- The chain form of a family of pair forms: the sum of the pair forms of the consecutive
pairs along the closed chain. -/
def form (β : ZMod K → QuadraticForm ℝ (V × V)) : QuadraticForm ℝ (ZMod K → V) :=
  ∑ j : ZMod K, (β j).comp (edge j)

theorem form_apply (β : ZMod K → QuadraticForm ℝ (V × V)) (w : ZMod K → V) :
    form β w = ∑ j : ZMod K, β j (w j, w (j + 1)) := by
  rw [form, sum_apply]
  rfl

end Def

/-! ### Cutting the chain of m + k periods -/

section Split

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (m k N : ℕ)

/-- The pair forms of the m-fold iterated chain. -/
def iter (β : ZMod N → QuadraticForm ℝ (V × V)) : ZMod (m * N) → QuadraticForm ℝ (V × V) :=
  fun j => β (ZMod.castHom (Dvd.intro_left m rfl) (ZMod N) j)

theorem iter_natCast (β : ZMod N → QuadraticForm ℝ (V × V)) (t : ℕ) :
    iter m N β (t : ZMod (m * N)) = β (t : ZMod N) := by
  rw [iter, map_natCast]

/-- The first m periods of a family on the chain of m + k periods. -/
def splitA (w : ZMod ((m + k) * N) → V) : ZMod (m * N) → V :=
  fun j => w ((j.val : ℕ) : ZMod ((m + k) * N))

/-- The last k periods of a family on the chain of m + k periods. -/
def splitB (w : ZMod ((m + k) * N) → V) : ZMod (k * N) → V :=
  fun j => w ((m * N + j.val : ℕ) : ZMod ((m + k) * N))

/-- The family on the chain of m + k periods made of a family of m periods followed by a
family of k periods. -/
def join (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) : ZMod ((m + k) * N) → V :=
  fun i => if i.val < m * N then y.1 ((i.val : ℕ) : ZMod (m * N))
    else y.2 ((i.val - m * N : ℕ) : ZMod (k * N))

omit [AddCommGroup V] [Module ℝ V] in
theorem join_apply (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) (i : ZMod ((m + k) * N)) :
    join m k N y i = if i.val < m * N then y.1 ((i.val : ℕ) : ZMod (m * N))
      else y.2 ((i.val - m * N : ℕ) : ZMod (k * N)) := rfl

/-- Cutting as a linear map. -/
def splitL : (ZMod ((m + k) * N) → V) →ₗ[ℝ] (ZMod (m * N) → V) × (ZMod (k * N) → V) where
  toFun w := (splitA m k N w, splitB m k N w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Joining as a linear map. -/
def joinL : ((ZMod (m * N) → V) × (ZMod (k * N) → V)) →ₗ[ℝ] (ZMod ((m + k) * N) → V) where
  toFun := join m k N
  map_add' y z := by
    funext i
    simp only [join, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> rfl
  map_smul' c y := by
    funext i
    simp only [join, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> rfl

omit [AddCommGroup V] [Module ℝ V] in
theorem join_natCast_lt (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) {t : ℕ}
    (ht : t < m * N) : join m k N y (t : ZMod ((m + k) * N)) = y.1 (t : ZMod (m * N)) := by
  have hK : (m + k) * N = m * N + k * N := add_mul m k N
  have hv : ((t : ZMod ((m + k) * N))).val = t := ZMod.val_natCast_of_lt (by omega)
  rw [join_apply, hv, ite_eq_left ht]

omit [AddCommGroup V] [Module ℝ V] in
theorem join_natCast_add (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) {s : ℕ}
    (hs : s < k * N) :
    join m k N y ((m * N + s : ℕ) : ZMod ((m + k) * N)) = y.2 (s : ZMod (k * N)) := by
  have hK : (m + k) * N = m * N + k * N := add_mul m k N
  have hv : (((m * N + s : ℕ) : ZMod ((m + k) * N))).val = m * N + s :=
    ZMod.val_natCast_of_lt (by omega)
  rw [join_apply, hv, ite_eq_right (by omega), Nat.add_sub_cancel_left]

variable [NeZero m] [NeZero k] [NeZero N]

omit [AddCommGroup V] [Module ℝ V] [NeZero k] in
/-- Cutting a joined family gives back the first family. -/
theorem splitA_join (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) :
    splitA m k N (join m k N y) = y.1 := by
  funext j
  rw [splitA, join_natCast_lt m k N y (ZMod.val_lt j), ZMod.natCast_zmod_val]

omit [AddCommGroup V] [Module ℝ V] [NeZero m] in
/-- Cutting a joined family gives back the second family. -/
theorem splitB_join (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) :
    splitB m k N (join m k N y) = y.2 := by
  funext j
  rw [splitB, join_natCast_add m k N y (ZMod.val_lt j), ZMod.natCast_zmod_val]

theorem splitL_joinL (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) :
    splitL m k N (joinL m k N y) = y :=
  Prod.ext (splitA_join m k N y) (splitB_join m k N y)

variable [NeZero (m + k)]

omit [NeZero m] [NeZero k] in
/-- Joining the two parts of a family gives back the family. -/
theorem joinL_splitL (w : ZMod ((m + k) * N) → V) : joinL m k N (splitL m k N w) = w := by
  funext i
  have hK : (m + k) * N = m * N + k * N := add_mul m k N
  have hi : i.val < (m + k) * N := ZMod.val_lt i
  change join m k N (splitA m k N w, splitB m k N w) i = w i
  rw [join_apply]
  by_cases h : i.val < m * N
  · rw [ite_eq_left h]
    change w ((((i.val : ℕ) : ZMod (m * N)).val : ℕ) : ZMod ((m + k) * N)) = w i
    rw [ZMod.val_natCast_of_lt h, ZMod.natCast_zmod_val]
  · rw [ite_eq_right h]
    change w ((m * N + (((i.val - m * N : ℕ) : ZMod (k * N))).val : ℕ) : ZMod ((m + k) * N)) = w i
    rw [ZMod.val_natCast_of_lt (by omega), Nat.add_sub_cancel' (Nat.le_of_not_lt h),
      ZMod.natCast_zmod_val]

omit [NeZero m] [NeZero k] in
theorem splitL_injective : Function.Injective (splitL (V := V) m k N) :=
  Function.LeftInverse.injective (joinL_splitL m k N)

omit [NeZero (m + k)] in
theorem joinL_injective : Function.Injective (joinL (V := V) m k N) :=
  Function.LeftInverse.injective (splitL_joinL m k N)

omit [AddCommGroup V] [Module ℝ V] [NeZero m] [NeZero k] [NeZero N] [NeZero (m + k)] in
/-- The first part of a family whose member at the index m N equals the member at 0. -/
theorem splitA_natCast (w : ZMod ((m + k) * N) → V)
    (hw : w ((m * N : ℕ) : ZMod ((m + k) * N)) = w 0) {t : ℕ} (ht : t ≤ m * N) :
    splitA m k N w (t : ZMod (m * N)) = w (t : ZMod ((m + k) * N)) := by
  rcases Nat.lt_or_eq_of_le ht with h | h
  · rw [splitA, ZMod.val_natCast_of_lt h]
  · subst h
    rw [splitA, ZMod.natCast_self, ZMod.val_zero, Nat.cast_zero, hw]

omit [AddCommGroup V] [Module ℝ V] [NeZero m] [NeZero k] [NeZero N] [NeZero (m + k)] in
/-- The second part of a family whose member at the index m N equals the member at 0. -/
theorem splitB_natCast (w : ZMod ((m + k) * N) → V)
    (hw : w ((m * N : ℕ) : ZMod ((m + k) * N)) = w 0) {s : ℕ} (hs : s ≤ k * N) :
    splitB m k N w (s : ZMod (k * N)) = w ((m * N + s : ℕ) : ZMod ((m + k) * N)) := by
  rcases Nat.lt_or_eq_of_le hs with h | h
  · rw [splitB, ZMod.val_natCast_of_lt h]
  · subst h
    rw [splitB, ZMod.natCast_self, ZMod.val_zero, Nat.add_zero, hw, ← add_mul,
      ZMod.natCast_self]

/-- **Cutting the chain form.** On the families whose member at the index m N equals the member
at 0, the chain form of m + k periods is the sum of the chain forms of the two parts. -/
theorem form_split (β : ZMod N → QuadraticForm ℝ (V × V)) (w : ZMod ((m + k) * N) → V)
    (hw : w ((m * N : ℕ) : ZMod ((m + k) * N)) = w 0) :
    form (iter (m + k) N β) w =
      form (iter m N β) (splitA m k N w) + form (iter k N β) (splitB m k N w) := by
  have hsplit : Finset.range ((m + k) * N) = Finset.range (m * N + k * N) := by rw [add_mul]
  rw [form_apply, form_apply, form_apply, sum_zmod, sum_zmod, sum_zmod, hsplit,
    Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t < m * N := Finset.mem_range.mp ht
    have e1 := splitA_natCast m k N w hw ht'.le
    have e2 := splitA_natCast m k N w hw (Nat.succ_le_of_lt ht')
    rw [Nat.cast_succ, Nat.cast_succ] at e2
    rw [e1, e2, iter_natCast, iter_natCast]
  · refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s < k * N := Finset.mem_range.mp hs
    have e1 := splitB_natCast m k N w hw hs'.le
    have e2 := splitB_natCast m k N w hw (Nat.succ_le_of_lt hs')
    rw [Nat.cast_succ, Nat.add_succ, Nat.cast_succ] at e2
    have hcast : ((m * N + s : ℕ) : ZMod N) = (s : ZMod N) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [e1, e2, iter_natCast, iter_natCast, hcast]

omit [AddCommGroup V] [Module ℝ V] [NeZero (m + k)] in
/-- A joined pair of families with equal members at 0 satisfies the constraint. -/
theorem join_constraint (y : (ZMod (m * N) → V) × (ZMod (k * N) → V)) (hy : y.1 0 = y.2 0) :
    join m k N y ((m * N : ℕ) : ZMod ((m + k) * N)) = join m k N y 0 := by
  have hmN : 0 < m * N := Nat.pos_of_ne_zero (NeZero.ne (m * N))
  have hkN : 0 < k * N := Nat.pos_of_ne_zero (NeZero.ne (k * N))
  have h1 := join_natCast_add m k N y hkN
  have h2 := join_natCast_lt m k N y hmN
  rw [Nat.add_zero, Nat.cast_zero] at h1
  rw [Nat.cast_zero, Nat.cast_zero] at h2
  rw [h1, h2, hy]

/-! ### The two estimates -/

/-- The constraint on the chain of m + k periods: the member at m N minus the member at 0. -/
def conA : (ZMod ((m + k) * N) → V) →ₗ[ℝ] V where
  toFun w := w ((m * N : ℕ) : ZMod ((m + k) * N)) - w 0
  map_add' _ _ := by
    simp only [Pi.add_apply]
    abel
  map_smul' _ _ := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

omit [NeZero m] [NeZero k] [NeZero N] [NeZero (m + k)] in
theorem mem_ker_conA {w : ZMod ((m + k) * N) → V} :
    w ∈ LinearMap.ker (conA (V := V) m k N) ↔ w ((m * N : ℕ) : ZMod ((m + k) * N)) = w 0 := by
  rw [LinearMap.mem_ker]
  exact sub_eq_zero

/-- The constraint on pairs of families: the difference of the members at 0. -/
def conB : ((ZMod (m * N) → V) × (ZMod (k * N) → V)) →ₗ[ℝ] V where
  toFun y := y.1 0 - y.2 0
  map_add' _ _ := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    abel
  map_smul' _ _ := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_sub]

omit [NeZero m] [NeZero k] [NeZero N] [NeZero (m + k)] in
theorem mem_ker_conB {y : (ZMod (m * N) → V) × (ZMod (k * N) → V)} :
    y ∈ LinearMap.ker (conB (V := V) m k N) ↔ y.1 0 = y.2 0 := by
  rw [LinearMap.mem_ker]
  exact sub_eq_zero

variable [FiniteDimensional ℝ V]

/-- The index of the chain of m + k periods is at most the sum of the indices plus dim V. -/
theorem sigNeg_form_add_le (β : ZMod N → QuadraticForm ℝ (V × V)) :
    sigNeg (form (iter (m + k) N β)) ≤
      sigNeg (form (iter m N β)) + sigNeg (form (iter k N β)) + finrank ℝ V := by
  have h1 := sigNeg_le_restrict_ker_add (form (iter (m + k) N β)) (conA (V := V) m k N)
  have h2 : sigNeg ((form (iter (m + k) N β)).restrict (LinearMap.ker (conA (V := V) m k N))) ≤
      sigNeg ((form (iter m N β)).prod (form (iter k N β))) := by
    refine sigNeg_le_of_injective _ _
      ((splitL m k N).comp (LinearMap.ker (conA (V := V) m k N)).subtype) ?_ fun x => ?_
    · exact (splitL_injective m k N).comp (Submodule.subtype_injective _)
    · rw [restrict_apply, form_split m k N β x ((mem_ker_conA m k N).mp x.2)]
      rfl
  rw [QuadraticForm.sigNeg_prod] at h2
  omega

/-- The sum of the indices is at most the index of the chain of m + k periods plus dim V. -/
theorem le_sigNeg_form_add (β : ZMod N → QuadraticForm ℝ (V × V)) :
    sigNeg (form (iter m N β)) + sigNeg (form (iter k N β)) ≤
      sigNeg (form (iter (m + k) N β)) + finrank ℝ V := by
  have h1 := sigNeg_le_restrict_ker_add ((form (iter m N β)).prod (form (iter k N β)))
    (conB (V := V) m k N)
  have h2 : sigNeg (((form (iter m N β)).prod (form (iter k N β))).restrict
      (LinearMap.ker (conB (V := V) m k N))) ≤ sigNeg (form (iter (m + k) N β)) := by
    refine sigNeg_le_of_injective _ _
      ((joinL m k N).comp (LinearMap.ker (conB (V := V) m k N)).subtype) ?_ fun y => ?_
    · exact (joinL_injective m k N).comp (Submodule.subtype_injective _)
    · have hy := (mem_ker_conB m k N).mp y.2
      change form (iter (m + k) N β) (join m k N (y : (ZMod (m * N) → V) × (ZMod (k * N) → V))) =
        _
      rw [form_split m k N β _ (join_constraint m k N _ hy), splitA_join, splitB_join,
        restrict_apply, QuadraticMap.prod_apply]
  rw [QuadraticForm.sigNeg_prod] at h1
  omega

end Split

/-! ### The index as a function of the number of periods -/

section Idx

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (N : ℕ) [NeZero N]

/-- The negative index of inertia of the chain form of m periods; zero for m = 0. -/
def idx (β : ZMod N → QuadraticForm ℝ (V × V)) (m : ℕ) : ℕ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    sigNeg (form (iter m N β))

theorem idx_eq (β : ZMod N → QuadraticForm ℝ (V × V)) (m : ℕ) [NeZero m] :
    idx N β m = sigNeg (form (iter m N β)) := by
  rw [idx, dite_eq_right (NeZero.ne m)]

variable [FiniteDimensional ℝ V]

/-- **The index of the iterates is subadditive up to dim V.** -/
theorem idx_add_le (β : ZMod N → QuadraticForm ℝ (V × V)) {m k : ℕ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) : idx N β (m + k) ≤ idx N β m + idx N β k + finrank ℝ V := by
  have : NeZero m := ⟨by omega⟩
  have : NeZero k := ⟨by omega⟩
  have : NeZero (m + k) := ⟨by omega⟩
  rw [idx_eq N β (m + k), idx_eq N β m, idx_eq N β k]
  exact sigNeg_form_add_le m k N β

/-- **The index of the iterates is superadditive up to dim V.** -/
theorem le_idx_add (β : ZMod N → QuadraticForm ℝ (V × V)) {m k : ℕ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) : idx N β m + idx N β k ≤ idx N β (m + k) + finrank ℝ V := by
  have : NeZero m := ⟨by omega⟩
  have : NeZero k := ⟨by omega⟩
  have : NeZero (m + k) := ⟨by omega⟩
  rw [idx_eq N β (m + k), idx_eq N β m, idx_eq N β k]
  exact le_sigNeg_form_add m k N β

/-- **The mean index.** There is Δ ≥ 0 with |I(m) - m Δ| ≤ dim V for all m ≥ 1. -/
theorem exists_mean (β : ZMod N → QuadraticForm ℝ (V × V)) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ ∀ m, 1 ≤ m → |(idx N β m : ℝ) - m * Δ| ≤ finrank ℝ V :=
  AlmostAdditive.exists_mean (fun _ _ hm hk => idx_add_le N β hm hk)
    (fun _ _ hm hk => le_idx_add N β hm hk)

/-- The index of the iterate of even order compared with twice the index of its half. -/
theorem idx_two_mul (β : ZMod N → QuadraticForm ℝ (V × V)) {m : ℕ} (hm : 1 ≤ m) :
    idx N β (2 * m) ≤ 2 * idx N β m + finrank ℝ V ∧
      2 * idx N β m ≤ idx N β (2 * m) + finrank ℝ V := by
  have h1 := idx_add_le N β hm hm
  have h2 := le_idx_add N β hm hm
  have e : m + m = 2 * m := (two_mul m).symm
  rw [e] at h1 h2
  constructor <;> omega

end Idx

end

end Finsler.ChainForm
