import Finsler.Algebra.ChainForm
import Finsler.Algebra.ChainIndexMul
import Finsler.Geometry.PolygonIterate

/-!
# Bounded iteration index forces nonnegative chain forms

A negative periodic variation can be repeated many times and cut to zero
at one vertex. The cut changes only two edge terms, independently of the
number of repetitions. This produces a negative based variation. Joining
independent based variations makes the negative index unbounded.

This elementary argument is used to remove the choice of a stabilizing
base iterate in the zero-mean-index branch of the surface proof.
-/

namespace Finsler.SurfaceChainIndex

open Module QuadraticMap Finsler.ChainForm

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (N : ℕ) [NeZero N] (β : ZMod N → QuadraticForm ℝ (V × V))

/-- Variations whose value at the marked vertex is zero. -/
def based (K : ℕ) : Submodule ℝ (ZMod K → V) := LinearMap.ker (LinearMap.proj 0)

omit [FiniteDimensional ℝ V] in
@[simp] theorem mem_based {K : ℕ} {w : ZMod K → V} :
    w ∈ based (V := V) K ↔ w 0 = 0 := Iff.rfl

/-- The index after fixing the marked vertex. -/
def basedIndex (m : ℕ) [NeZero m] : ℕ :=
  sigNeg ((form (iter m N β)).restrict (based (m * N)))

/-- Fixing a vertex cannot increase the negative index. -/
theorem basedIndex_le (m : ℕ) [NeZero m] : basedIndex N β m ≤ idx N β m := by
  rw [idx_eq]
  exact sigNeg_le_of_injective _ _ (based (m * N)).subtype
    (Submodule.subtype_injective _) (fun _ => rfl)

/-- Joining based variations has no matching constraint, so their indices
are superadditive without a dimension error. -/
theorem basedIndex_add (m k : ℕ) [NeZero m] [NeZero k] [NeZero (m + k)] :
    basedIndex N β m + basedIndex N β k ≤ basedIndex N β (m + k) := by
  let J : (based (V := V) (m * N) × based (V := V) (k * N)) →ₗ[ℝ]
      based (V := V) ((m + k) * N) :=
    (((joinL m k N).comp
      ((based (m * N)).subtype.prodMap (based (k * N)).subtype)).codRestrict
        (based ((m + k) * N)) fun y => by
          change join m k N (y.1.val, y.2.val) 0 = 0
          have h := join_natCast_lt m k N (y.1.val, y.2.val)
            (Nat.pos_of_ne_zero (NeZero.ne (m * N)))
          simpa only [Nat.cast_zero, (show y.1.val 0 = 0 from y.1.property)] using h)
  have hJ : Function.Injective J := by
    intro x y h
    have h' := joinL_injective m k N (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h'))
      (Subtype.ext (congrArg Prod.snd h'))
  have h := sigNeg_le_of_injective
    (((form (iter m N β)).restrict (based (m * N))).prod
      ((form (iter k N β)).restrict (based (k * N))))
    ((form (iter (m + k) N β)).restrict (based ((m + k) * N))) J hJ (fun y => by
      change form (iter (m + k) N β) (join m k N (y.1.val,y.2.val)) = _
      rw [form_split m k N β _ (join_constraint m k N _
        (y.1.property.trans y.2.property.symm)), splitA_join, splitB_join]
      rfl)
  rw [QuadraticForm.sigNeg_prod] at h
  exact h

/-- Independent copies of a based negative subspace give linear index growth. -/
theorem mul_basedIndex_le (m k : ℕ) [NeZero m] (hk : 1 ≤ k) :
    haveI : NeZero k := ⟨by omega⟩
    k * basedIndex N β m ≤ basedIndex N β (k * m) := by
  have hk' : NeZero k := ⟨by omega⟩
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have : NeZero k := ⟨by omega⟩
    have : NeZero (k * m + m) := ⟨by
      have := Nat.pos_of_ne_zero (NeZero.ne m)
      omega⟩
    have h := basedIndex_add N β (k * m) m
    simpa only [Nat.add_mul, one_mul] using
      (Nat.add_le_add_right (ih inferInstance) (basedIndex N β m)).trans h

/-- Bounded periodic index rules out every negative based variation. -/
theorem basedIndex_eq_zero_of_bounded (B : ℕ)
    (hbound : ∀ m : ℕ, ∀ [NeZero m], idx N β m ≤ B) (m : ℕ) [NeZero m] :
    basedIndex N β m = 0 := by
  have h := (mul_basedIndex_le N β m (B + 1) (by omega)).trans
    ((basedIndex_le N β ((B + 1) * m)).trans (hbound _))
  nlinarith

omit [FiniteDimensional ℝ V] in
/-- Repeating a variation repeats its unnormalized chain energy. -/
theorem form_repeat (m : ℕ) [NeZero m] (w : ZMod N → V) :
    form (iter m N β) (Finsler.PolygonIterate.iterate m N w) =
      (m : ℝ) * form β w := by
  rw [form_apply, form_apply, sum_zmod, sum_zmod]
  have h := Finsler.PolygonIterate.sum_range_mul m N
    (fun j => β j (w j, w (j + 1)))
  simp only [nsmul_eq_mul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iter_natCast, Finsler.PolygonIterate.iterate_natCast,
    Finsler.PolygonIterate.iterate_natCast_add_one]

omit [FiniteDimensional ℝ V] in
/-- Cutting a periodic variation to zero at one vertex changes exactly
the two adjacent edge terms. -/
theorem form_update_zero {K : ℕ} [NeZero K] (hK : 2 ≤ K)
    (b : ZMod K → QuadraticForm ℝ (V × V)) (w : ZMod K → V) :
    form b (Function.update w 0 0) = form b w +
      (b 0 (0, w 1) - b 0 (w 0, w 1)) +
      (b (-1) (w (-1), 0) - b (-1) (w (-1), w 0)) := by
  classical
  have : Fact (1 < K) := ⟨by omega⟩
  have hneg : (-1 : ZMod K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have h0 : (0 : ZMod K) ≠ -1 := Ne.symm hneg
  have he : ∀ j : ZMod K,
      b j (Function.update w 0 0 j, Function.update w 0 0 (j + 1)) =
        b j (w j, w (j + 1)) +
          (if j = 0 then b 0 (0, w 1) - b 0 (w 0, w 1) else 0) +
          (if j = -1 then b (-1) (w (-1), 0) - b (-1) (w (-1), w 0) else 0) := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [h0]
    · by_cases hj' : j = -1
      · subst j
        simp [hneg]
      · have hs : j + 1 ≠ 0 := by
          intro h
          apply hj'
          calc j = (j + 1) - 1 := by abel
               _ = -1 := by rw [h, zero_sub]
        simp [hj, hj', hs]
  rw [form_apply, form_apply]
  simp_rw [he, Finset.sum_add_distrib]
  simp

omit [FiniteDimensional ℝ V] in
/-- A negative periodic variation produces a negative based variation
after sufficiently many repetitions. Only a fixed boundary cost is paid. -/
theorem exists_negative_based_repeat (hN : 2 ≤ N) (w : ZMod N → V)
    (hw : form β w < 0) :
    ∃ m : ℕ, ∃ hm : NeZero m,
      letI := hm
      ∃ z : based (V := V) (m * N), (form (iter m N β)).restrict (based (m * N)) z < 0 := by
  classical
  let C := (β 0 (0, w 1) - β 0 (w 0, w 1)) +
    (β (-1) (w (-1), 0) - β (-1) (w (-1), w 0))
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (C / (-form β w)))
  have hm1 : 1 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmpos : 1 ≤ m := by exact_mod_cast hm1.le
  have hmne : NeZero m := ⟨by omega⟩
  have hc : C < (m : ℝ) * (-form β w) :=
    (div_lt_iff₀ (neg_pos.mpr hw)).mp ((le_max_right _ _).trans_lt hm)
  let z := Function.update (Finsler.PolygonIterate.iterate m N w) 0 0
  have hz : z ∈ based (m * N) := by simp [z]
  refine ⟨m, hmne, ⟨z, hz⟩, ?_⟩
  have hcut := form_update_zero (V := V) (K := m * N) (by nlinarith)
    (iter m N β) (Finsler.PolygonIterate.iterate m N w)
  rw [form_repeat] at hcut
  simp only [iter, Finsler.PolygonIterate.iterate, Finsler.PolygonIterate.red,
    map_zero, map_one, map_neg] at hcut
  change form (iter m N β) z < 0
  change form (iter m N β) z = _ at hcut
  dsimp [C] at hc
  linarith

/-- If the indices of all repetitions are bounded, the original chain
form is nonnegative. -/
theorem form_nonneg_of_bounded (hN : 2 ≤ N) (B : ℕ)
    (hbound : ∀ m : ℕ, ∀ [NeZero m], idx N β m ≤ B) (w : ZMod N → V) :
    0 ≤ form β w := by
  by_contra hn
  obtain ⟨m, hm, z, hz⟩ := exists_negative_based_repeat N β hN w (lt_of_not_ge hn)
  have : NeZero m := hm
  have hzero := basedIndex_eq_zero_of_bounded N β B hbound m
  have hp := (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero
    ((form (iter m N β)).restrict (based (m * N)))).mpr hzero z
  exact (not_lt_of_ge hp) hz

/-- Boundedness of the entire iteration sequence forces every positive
iterate index to vanish, not merely to stabilize at a positive value. -/
theorem idx_eq_zero_of_bounded (hN : 2 ≤ N) (B : ℕ)
    (hbound : ∀ m : ℕ, ∀ [NeZero m], idx N β m ≤ B) (m : ℕ) [NeZero m] :
    idx N β m = 0 := by
  rw [idx_eq]
  apply (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero _).mp
  apply form_nonneg_of_bounded (m * N) (iter m N β) (by
    have := Nat.pos_of_ne_zero (NeZero.ne m)
    nlinarith) B
  intro k hk
  rw [Finsler.ChainIndexMul.idx_mul]
  exact hbound (m * k)

end
end Finsler.SurfaceChainIndex
