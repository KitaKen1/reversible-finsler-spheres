import Finsler.Analysis.H1JoinContinuity
import Finsler.Analysis.IntervalH1Iteration

/-!
# Finite loop blocks for the surface iteration argument

The input consists of actual H¹ sphere loops with a common basepoint, which
is allowed to vary. Concatenation gives a jointly continuous H¹ loop, running
each of the `m + 1` blocks for equal time. Its exact energy is
`(m + 1) * ∑ i, E(uᵢ)`. A deficit in any one block is amplified by `m + 1`.

This constructs the repeated-block map used for the local ball in DPMMS,
proof of Theorem 5.4, equation (5.7). It does not assert that its image is
a nonzero local homology class or provide the enlarged-domain filling.
-/

namespace Finsler.HingstonBlocks

open Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.H1LoopJoin Finsler.H1JoinContinuity Finsler.SobolevEnergy

noncomputable section

variable {n m : ℕ}

/-- Nonempty ordered blocks whose common basepoint may vary with the input. -/
def Blocks (n m : ℕ) :=
  {u : Fin (m + 1) → SphereLoop n // ∀ i, basepoint (u i) = basepoint (u 0)}

instance : TopologicalSpace (Blocks n m) := inferInstanceAs
  (TopologicalSpace {u : Fin (m + 1) → SphereLoop n //
    ∀ i, basepoint (u i) = basepoint (u 0)})

private def initialBlocks (u : Blocks n (m + 1)) : Blocks n m :=
  ⟨fun i => u.val i.castSucc, fun i => u.property i.castSucc⟩

private def split (m : ℕ) : ℝ := ((m : ℝ) + 1) / ((m : ℝ) + 2)

private theorem split_pos (m : ℕ) : 0 < split m := by
  unfold split
  positivity

private theorem split_lt_one (m : ℕ) : split m < 1 := by
  unfold split
  apply (div_lt_one (by positivity)).mpr
  linarith

private def basedConcat : (m : ℕ) → (u : Blocks n m) →
    {v : SphereLoop n // basepoint v = basepoint (u.val 0)}
  | 0, u => ⟨u.val 0, rfl⟩
  | m + 1, u =>
    let v := basedConcat m (initialBlocks u)
    let h := v.property.trans (u.property (Fin.last (m + 1))).symm
    ⟨join (split m) (split_pos m) (split_lt_one m) v.val (u.val (Fin.last (m + 1))) h,
      (basepoint_join _ _ _ _ _ _).trans v.property⟩

/-- Equal-time concatenation of the `m + 1` actual loops. -/
def concat (u : Blocks n m) : SphereLoop n := (basedConcat m u).val

theorem basepoint_concat (u : Blocks n m) :
    basepoint (concat u) = basepoint (u.val 0) := (basedConcat m u).property

private theorem concat_succ (u : Blocks n (m + 1)) :
    concat u = join (split m) (split_pos m) (split_lt_one m)
      (concat (initialBlocks u)) (u.val (Fin.last (m + 1)))
      ((basepoint_concat (initialBlocks u)).trans (u.property (Fin.last (m + 1))).symm) := rfl

private theorem continuous_prefix : Continuous (initialBlocks : Blocks n (m + 1) → Blocks n m) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply i.castSucc).comp continuous_subtype_val

/-- Strong H¹ continuity, including variation of the common basepoint. -/
theorem continuous_concat (n m : ℕ) : Continuous (concat : Blocks n m → SphereLoop n) := by
  induction m with
  | zero => exact (continuous_apply 0).comp continuous_subtype_val
  | succ m ih =>
    have hp : Continuous (fun u : Blocks n (m + 1) =>
        (⟨(concat (initialBlocks u), u.val (Fin.last (m + 1))),
          (basepoint_concat (initialBlocks u)).trans (u.property (Fin.last (m + 1))).symm⟩ :
          composable n)) :=
      ((ih.comp continuous_prefix).prodMk
        ((continuous_apply (Fin.last (m + 1))).comp continuous_subtype_val)).subtype_mk _
    exact ((continuous_join (split m) (split_pos m) (split_lt_one m)).comp hp).congr
      (fun u => (concat_succ u).symm)

/-- DPMMS's concatenation energy identity for genuine H¹ loops. -/
theorem energy_concat (F : ReversibleMetric n) (u : Blocks n m) :
    energy F (concat u) = ((m : ℝ) + 1) * ∑ i, energy F (u.val i) := by
  induction m with
  | zero => simp [concat, basedConcat]
  | succ m ih =>
    rw [concat_succ, energy_join, ih]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [initialBlocks, split, Nat.cast_add, Nat.cast_one]
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    have hm' : (m : ℝ) + 2 ≠ 0 := by positivity
    have hs : 1 - ((m : ℝ) + 1) / ((m : ℝ) + 2) = 1 / ((m : ℝ) + 2) := by
      field_simp
      ring
    rw [hs]
    field_simp
    ring

/-- Uniform energy bounds on the blocks give the expected quadratic bound. -/
theorem energy_concat_le (F : ReversibleMetric n) (u : Blocks n m) {L : ℝ}
    (hL : ∀ i, energy F (u.val i) ≤ L) :
    energy F (concat u) ≤ ((m : ℝ) + 1) ^ 2 * L := by
  rw [energy_concat]
  have hs : ∑ i, energy F (u.val i) ≤ ((m : ℝ) + 1) * L := by
    calc
      _ ≤ ∑ _ : Fin (m + 1), L := Finset.sum_le_sum fun i _ => hL i
      _ = _ := by simp
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (m : ℝ) + 1)]

/-- A deficit in any selected block is multiplied by the total block count.
This is the boundary-energy estimate needed for product local balls. -/
theorem energy_concat_deficit (F : ReversibleMetric n) (u : Blocks n m)
    {L δ : ℝ} (j : Fin (m + 1)) (hL : ∀ i, energy F (u.val i) ≤ L)
    (hj : energy F (u.val j) ≤ L - δ) :
    energy F (concat u) ≤ ((m : ℝ) + 1) ^ 2 * L - ((m : ℝ) + 1) * δ := by
  classical
  have hs : δ ≤ ∑ i, (L - energy F (u.val i)) := by
    calc
      δ ≤ L - energy F (u.val j) := by linarith
      _ ≤ ∑ i, (L - energy F (u.val i)) :=
        Finset.single_le_sum (fun i _ => sub_nonneg.mpr (hL i)) (Finset.mem_univ j)
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hs
  rw [energy_concat]
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (m : ℝ) + 1)]

/-- If one block is strictly below the common maximum, so is the concatenation. -/
theorem energy_concat_lt (F : ReversibleMetric n) (u : Blocks n m) {L : ℝ}
    (hL : ∀ i, energy F (u.val i) ≤ L) (hstrict : ∃ i, energy F (u.val i) < L) :
    energy F (concat u) < ((m : ℝ) + 1) ^ 2 * L := by
  obtain ⟨j, hj⟩ := hstrict
  have hd := energy_concat_deficit F u j hL (δ := L - energy F (u.val j)) (by linarith)
  have hp : 0 < ((m : ℝ) + 1) * (L - energy F (u.val j)) :=
    mul_pos (by positivity) (sub_pos.mpr hj)
  linarith

private theorem join_injective {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Function.Injective (joinMap (n := n) a ha0 ha1) := by
  intro u v huv
  have hd := congrArg (fun w : SphereLoop n => (w.data : Space n)) huv
  change SobolevConcat.concat (u.val.1.data : Space n) (u.val.2.data : Space n) ha0 ha1 =
    SobolevConcat.concat (v.val.1.data : Space n) (v.val.2.data : Space n) ha0 ha1 at hd
  have hl := congrArg (fun w : Space n => SobolevAffine.restrict w
    SobolevConcat.zero_mem_unit (SobolevConcat.split_mem ha0 ha1) ha0.le) hd
  have hr := congrArg (fun w : Space n => SobolevAffine.restrict w
    (SobolevConcat.split_mem ha0 ha1) SobolevConcat.one_mem_unit ha1.le) hd
  rw [SobolevConcat.restrict_concat_left, SobolevConcat.restrict_concat_left] at hl
  rw [SobolevConcat.restrict_concat_right _ _ ha0 ha1 (end_match _ _ u.property),
    SobolevConcat.restrict_concat_right _ _ ha0 ha1 (end_match _ _ v.property)] at hr
  exact Subtype.ext (Prod.ext ((sphereLoop_data_isometry n).injective hl)
    ((sphereLoop_data_isometry n).injective hr))

/-- Restricting to the equal-time intervals recovers every input loop. In
particular no product parameters are identified by concatenation. -/
theorem concat_injective (n m : ℕ) : Function.Injective (concat : Blocks n m → SphereLoop n) := by
  induction m with
  | zero =>
    intro u v h
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact h
  | succ m ih =>
    intro u v h
    rw [concat_succ, concat_succ] at h
    let pu : composable n := ⟨(concat (initialBlocks u), u.val (Fin.last (m + 1))),
      (basepoint_concat (initialBlocks u)).trans (u.property (Fin.last (m + 1))).symm⟩
    let pv : composable n := ⟨(concat (initialBlocks v), v.val (Fin.last (m + 1))),
      (basepoint_concat (initialBlocks v)).trans (v.property (Fin.last (m + 1))).symm⟩
    have he : pu = pv := @join_injective n (split m) (split_pos m) (split_lt_one m) pu pv h
    have hl := congrArg (fun z : composable n => z.val.1) he
    have hr := congrArg (fun z : composable n => z.val.2) he
    have hp := ih hl
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hr
    · exact congrArg (fun z : Blocks n m => z.val j) hp

theorem basepoint_iterate (u : SphereLoop n) (k : ℕ) (hk : k ≠ 0) :
    basepoint (SobolevIteration.iterateSphere u k hk) = basepoint u := by
  change continuousRepresentative (SobolevIteration.iterateData u.data k hk) 0 =
    continuousRepresentative (u.data : Space n) 0
  rw [SobolevIteration.representative_iterateData _ _ _ (by norm_num), mul_zero]
  exact SobolevCircleRepresentative.realMap_eqOn u.data (by norm_num)

private theorem join_iteration (u : SphereLoop n) (m : ℕ) :
    join (split m) (split_pos m) (split_lt_one m)
      (SobolevIteration.iterateSphere u (m + 1) (by omega)) u
      (basepoint_iterate u (m + 1) (by omega)) =
    SobolevIteration.iterateSphere u (m + 2) (by omega) := by
  apply (sphereLoop_data_isometry n).injective
  apply h1_eq_of_representative_eq
  intro t
  change continuousRepresentative
    (SobolevConcat.concat
      (SobolevIteration.iterateData u.data (m + 1) (by omega)) (u.data : Space n)
      (split_pos m) (split_lt_one m)) t =
    continuousRepresentative (SobolevIteration.iterateData u.data (m + 2) (by omega)) t
  rw [SobolevIteration.representative_iterateData _ _ _ t.property]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm' : (m : ℝ) + 2 ≠ 0 := by positivity
  by_cases ht : (t : ℝ) ≤ split m
  · rw [SobolevConcat.representative_concat_left _ _ (split_pos m) (split_lt_one m)
      ⟨t.property.1, ht⟩,
      SobolevIteration.representative_iterateData _ _ _
        (H1ConcatContinuity.left_time_mem (split_pos m) t.property ht)]
    congr 1
    simp only [split, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp
  · have hge := (lt_of_not_ge ht).le
    have hend : continuousRepresentative (SobolevIteration.iterateData u.data (m + 1)
        (by omega)) 1 = continuousRepresentative (u.data : Space n) 0 := by
      rw [SobolevIteration.representative_iterateData _ _ _ (by norm_num), mul_one]
      calc
        _ = SobolevCircleRepresentative.realMap u.data 0 := by
          simpa only [mul_one] using
            (SobolevCircleRepresentative.realMap_periodic u.data).nat_mul_eq (m + 1)
        _ = _ := SobolevCircleRepresentative.realMap_eqOn u.data (by norm_num)
    rw [SobolevConcat.representative_concat_right _ _ (split_pos m) (split_lt_one m)
      hend ⟨hge, t.property.2⟩]
    rw [← SobolevCircleRepresentative.realMap_eqOn u.data
      (H1ConcatContinuity.right_time_mem (split_lt_one m) t.property hge)]
    have hr : SobolevConcat.rightMap (split m) t =
        ((m + 2 : ℕ) : ℝ) * t - ((m + 1 : ℕ) : ℝ) := by
      simp only [SobolevConcat.rightMap, split,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      field_simp
      ring
    rw [hr]
    simpa only [mul_one] using
      (SobolevCircleRepresentative.realMap_periodic u.data).sub_nat_mul_eq
        (x := ((m + 2 : ℕ) : ℝ) * t) (m + 1)

/-- Joining two integer iterates with time weights equal to their iteration
counts gives exactly the sum iterate, including its parametrization. -/
theorem join_iterates (u : SphereLoop n) (k l : ℕ) (hk : k ≠ 0) (hl : l ≠ 0) :
    join ((k : ℝ) / ((k : ℝ) + l))
      (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))
        (add_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))
          (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl))))
      ((div_lt_one (add_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)))).mpr
          (by have : (0 : ℝ) < l := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl); linarith))
      (SobolevIteration.iterateSphere u k hk) (SobolevIteration.iterateSphere u l hl)
      ((basepoint_iterate u k hk).trans (basepoint_iterate u l hl).symm) =
    SobolevIteration.iterateSphere u (k + l) (by omega) := by
  let α : ℝ := (k : ℝ) / ((k : ℝ) + l)
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hl' : (0 : ℝ) < l := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)
  have hs : (0 : ℝ) < (k : ℝ) + l := add_pos hk' hl'
  have hα : 0 < α := div_pos hk' hs
  have hα' : α < 1 := (div_lt_one hs).mpr (by linarith)
  apply (sphereLoop_data_isometry n).injective
  apply h1_eq_of_representative_eq
  intro t
  change continuousRepresentative
    (SobolevConcat.concat (SobolevIteration.iterateData u.data k hk)
      (SobolevIteration.iterateData u.data l hl) hα hα') t =
    continuousRepresentative (SobolevIteration.iterateData u.data (k + l) (by omega)) t
  rw [SobolevIteration.representative_iterateData _ _ _ t.property]
  by_cases ht : (t : ℝ) ≤ α
  · rw [SobolevConcat.representative_concat_left _ _ hα hα' ⟨t.property.1, ht⟩,
      SobolevIteration.representative_iterateData _ _ _
        (H1ConcatContinuity.left_time_mem hα t.property ht)]
    congr 1
    simp only [α, Nat.cast_add]
    field_simp
  · have hge := (lt_of_not_ge ht).le
    have hm := end_match (SobolevIteration.iterateSphere u k hk)
      (SobolevIteration.iterateSphere u l hl)
      ((basepoint_iterate u k hk).trans (basepoint_iterate u l hl).symm)
    change continuousRepresentative (SobolevIteration.iterateData u.data k hk) 1 =
      continuousRepresentative (SobolevIteration.iterateData u.data l hl) 0 at hm
    rw [SobolevConcat.representative_concat_right _ _ hα hα' hm ⟨hge, t.property.2⟩,
      SobolevIteration.representative_iterateData _ _ _
        (H1ConcatContinuity.right_time_mem hα' t.property hge)]
    have hr : (l : ℝ) * SobolevConcat.rightMap α t =
        ((k + l : ℕ) : ℝ) * t - (k : ℝ) := by
      have he : 1 - α = (l : ℝ) / ((k : ℝ) + l) := by
        dsimp [α]
        field_simp
        ring
      rw [SobolevConcat.rightMap, he]
      dsimp [α]
      push_cast
      field_simp
      ring
    rw [hr]
    simpa only [mul_one] using
      (SobolevCircleRepresentative.realMap_periodic u.data).sub_nat_mul_eq
        (x := ((k + l : ℕ) : ℝ) * t) k

/-- The diagonal blocks consist of repeated copies of the same actual loop. -/
def diagonal (u : SphereLoop n) (m : ℕ) : Blocks n m := ⟨fun _ => u, fun _ => rfl⟩

/-- The diagonal of the repeated-block construction is exactly the existing
integer-iteration map, including its parametrization. -/
theorem concat_diagonal (u : SphereLoop n) (m : ℕ) :
    concat (diagonal u m) = SobolevIteration.iterateSphere u (m + 1) (by omega) := by
  induction m with
  | zero => exact (SobolevIteration.iterateSphere_one u).symm
  | succ m ih =>
    rw [concat_succ]
    change join (split m) (split_pos m) (split_lt_one m)
      (concat (diagonal u m)) u _ = _
    simpa only [ih] using join_iteration u m

section Families

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : C(X × Y, SphereLoop n))
    (hbase : ∀ x y z, basepoint (φ (x, y)) = basepoint (φ (x, z)))

/-- The product parameter domain, with a single common base parameter and
independent transverse parameters in the blocks. -/
def familyBlocks (m : ℕ) : C(X × (Fin (m + 1) → Y), Blocks n m) :=
  ⟨fun z => ⟨fun i => φ (z.1, z.2 i), fun i => hbase z.1 (z.2 i) (z.2 0)⟩,
    (continuous_pi fun i => φ.continuous.comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).subtype_mk _⟩

/-- The actual repeated-block family. The common base parameter may vary. -/
def family (m : ℕ) : C(X × (Fin (m + 1) → Y), SphereLoop n) :=
  (⟨concat, continuous_concat n m⟩ : C(Blocks n m, SphereLoop n)).comp
    (familyBlocks φ hbase m)

/-- The center of the repeated local family is the actual iterate of its
original center, not merely a loop with the same energy. -/
theorem family_diagonal (z : X × Y) (m : ℕ) :
    family φ hbase m (z.1, fun _ => z.2) =
      SobolevIteration.iterateSphere (φ z) (m + 1) (by omega) :=
  concat_diagonal (φ z) m

theorem energy_family (F : ReversibleMetric n) (z : X × (Fin (m + 1) → Y)) :
    energy F (family φ hbase m z) =
      ((m : ℝ) + 1) * ∑ i, energy F (φ (z.1, z.2 i)) :=
  energy_concat F (familyBlocks φ hbase m z)

/-- A unique strict maximum of the original local family remains a unique
strict maximum at the repeated parameter in the product family. -/
theorem energy_family_lt (F : ReversibleMetric n) {L : ℝ} {z₀ : X × Y}
    (hL : ∀ z, energy F (φ z) ≤ L)
    (hstrict : ∀ z, z ≠ z₀ → energy F (φ z) < L)
    (z : X × (Fin (m + 1) → Y)) (hne : z ≠ (z₀.1, fun _ => z₀.2)) :
    energy F (family φ hbase m z) < ((m : ℝ) + 1) ^ 2 * L := by
  apply energy_concat_lt F (familyBlocks φ hbase m z)
  · exact fun i => hL (z.1, z.2 i)
  · by_contra h
    apply hne
    have hall : ∀ i, (z.1, z.2 i) = z₀ := by
      intro i
      by_contra hi
      exact h ⟨i, hstrict _ hi⟩
    apply Prod.ext
    · exact congrArg (fun p : X × Y => p.1) (hall 0)
    · funext i
      exact congrArg (fun p : X × Y => p.2) (hall i)

/-- An injective original parameterization gives an injective repeated-block
parameterization, including its common base parameter. -/
theorem family_injective (hφ : Function.Injective φ) :
    Function.Injective (family φ hbase m) := by
  intro z w h
  have hb := concat_injective n m h
  have hi : ∀ i, (z.1, z.2 i) = (w.1, w.2 i) := fun i =>
    hφ (congrArg (fun u : Blocks n m => u.val i) hb)
  apply Prod.ext
  · exact congrArg (fun p : X × Y => p.1) (hi 0)
  · funext i
    exact congrArg (fun p : X × Y => p.2) (hi i)

/-- For compact parameter disks, the repeated-block construction is an actual
topological embedding into the strong H¹ loop space. -/
theorem family_isClosedEmbedding [CompactSpace X] [CompactSpace Y]
    (hφ : Function.Injective φ) : Topology.IsClosedEmbedding (family φ hbase m) :=
  (family φ hbase m).continuous.isClosedEmbedding (family_injective φ hbase hφ)

/-- Compactness produces a single positive boundary deficit before the block
count is chosen. Any product face with a transverse parameter in the given
compact boundary set then lies below the repeated critical energy by at least
`(m + 1) * δ`. The constant `δ` is independent of `m`. -/
theorem exists_boundary_deficit (F : ReversibleMetric n) [CompactSpace X]
    {B : Set Y} (hB : IsCompact B) {L : ℝ}
    (hL : ∀ z, energy F (φ z) ≤ L)
    (hstrict : ∀ x y, y ∈ B → energy F (φ (x, y)) < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (z : X × (Fin (m + 1) → Y)),
      (∃ i, z.2 i ∈ B) → energy F (family φ hbase m z) ≤
        ((m : ℝ) + 1) ^ 2 * L - ((m : ℝ) + 1) * δ := by
  have hc : IsCompact ((Set.univ : Set X) ×ˢ B) := isCompact_univ.prod hB
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x y, y ∈ B →
      energy F (φ (x, y)) ≤ L - δ := by
    by_cases hne : ((Set.univ : Set X) ×ˢ B).Nonempty
    · obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn hne
        ((SobolevEnergy.energy_continuous F).comp φ.continuous).continuousOn
      refine ⟨L - energy F (φ z), sub_pos.mpr (hstrict z.1 z.2 hz.2), ?_⟩
      intro x y hy
      have hh := hmax (show (x, y) ∈ (Set.univ : Set X) ×ˢ B from ⟨Set.mem_univ _, hy⟩)
      change energy F (φ (x, y)) ≤ energy F (φ z) at hh
      linarith
    · exact ⟨1, zero_lt_one, fun x y hy => False.elim (hne ⟨(x, y), Set.mem_univ _, hy⟩)⟩
  refine ⟨δ, hδ, fun m z ⟨j, hj⟩ => ?_⟩
  exact energy_concat_deficit F (familyBlocks φ hbase m z) j
    (fun i => hL (z.1, z.2 i)) (hbound z.1 (z.2 j) hj)

/-- Product faces inherited from a boundary subset of the original parameters. -/
def familyBoundary (B : Set (X × Y)) (m : ℕ) : Set (X × (Fin (m + 1) → Y)) :=
  {z | ∃ i, (z.1, z.2 i) ∈ B}

/-- A length cut strictly above the repeated critical length contains the
entire repeated family, including its center. -/
theorem family_mem_lev (F : ReversibleMetric n) {l a : ℝ} (hl : 0 < l)
    (ha : ((m : ℝ) + 1) * l < a) (hL : ∀ z, energy F (φ z) ≤ l ^ 2)
    (z : X × (Fin (m + 1) → Y)) : family φ hbase m z ∈ BorelLoop.lev F a := by
  have hp : 0 < ((m : ℝ) + 1) * l := mul_pos (by positivity) hl
  apply (Birkhoff.mem_lev_iff (hp.trans ha) _).mpr
  calc
    _ ≤ ((m : ℝ) + 1) ^ 2 * l ^ 2 :=
      energy_concat_le F (familyBlocks φ hbase m z) (fun i => hL _)
    _ = (((m : ℝ) + 1) * l) ^ 2 := by ring
    _ < a ^ 2 := by nlinarith

/-- The product boundary maps strictly below the repeated critical length.
This is the boundary condition for a genuine relative sublevel map. -/
theorem family_boundary_mem (F : ReversibleMetric n) {l : ℝ} (hl : 0 < l)
    {B : Set (X × Y)} (hL : ∀ z, energy F (φ z) ≤ l ^ 2)
    (hB : ∀ z ∈ B, energy F (φ z) < l ^ 2)
    (z : X × (Fin (m + 1) → Y)) (hz : z ∈ familyBoundary B m) :
    family φ hbase m z ∈ BorelLoop.lev F (((m : ℝ) + 1) * l) := by
  apply (Birkhoff.mem_lev_iff (mul_pos (by positivity) hl) _).mpr
  obtain ⟨j, hj⟩ := hz
  have he := energy_concat_lt F (familyBlocks φ hbase m z)
    (fun i => hL _) ⟨j, hB _ hj⟩
  change energy F (concat (familyBlocks φ hbase m z)) < (((m : ℝ) + 1) * l) ^ 2
  rw [mul_pow]
  exact he

end Families

section RelativeFamily

open CategoryTheory

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : C(X × Y, SphereLoop n))
    (hbase : ∀ x y z, basepoint (φ (x, y)) = basepoint (φ (x, z)))
    (F : ReversibleMetric n) {l a : ℝ} (hl : 0 < l)
    (ha : ((m : ℝ) + 1) * l < a) {B : Set (X × Y)}
    (hL : ∀ z, energy F (φ z) ≤ l ^ 2)
    (hB : ∀ z ∈ B, energy F (φ z) < l ^ 2)

/-- The repeated local family as a map of actual topological pairs, from
the parameter domain modulo its product boundary to the two energy sublevels.
It is ready to induce the relative homology map; nonvanishing of that map is
not asserted here. -/
def familyPairMap :
    TopPair.ofSubset (X := TopCat.of (X × (Fin (m + 1) → Y))) (familyBoundary B m) ⟶
      BorelLoop.pairOf (BorelLoop.lev_mono F ha.le) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun z => ⟨family φ hbase m z, family_mem_lev φ hbase F hl ha hL z⟩,
      (family φ hbase m).continuous.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun z => ⟨family φ hbase m z.val,
      family_boundary_mem φ hbase F hl hL hB z.val z.property⟩,
      ((family φ hbase m).continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (by ext z; rfl)

/-- The map of pairs uses exactly the constructed H¹ loop family. -/
theorem familyPairMap_apply (z : X × (Fin (m + 1) → Y)) :
    (TopPair.Hom.fst (familyPairMap φ hbase F hl ha hL hB) z).val =
      family φ hbase m z := rfl

end RelativeFamily

end

end Finsler.HingstonBlocks
