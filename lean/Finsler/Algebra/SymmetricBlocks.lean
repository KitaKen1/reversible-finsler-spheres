module

public import Finsler.Analysis.InvariantIndex

/-! Block decomposition of a symmetric bilinear function invariant under a linear map of finite
order. Let ρ be a linear map of a real vector space with ρ^k = 1, k > 0. The fixed vectors of ρ
and the kernel of the sum 1 + ρ + ⋯ + ρ^{k−1} are complementary subspaces: a vector is the sum of
the average of its orbit and a vector with vanishing orbit sum. If a bilinear function β is
invariant under ρ, a fixed vector is β-orthogonal to every vector with vanishing orbit sum. For
symmetric β on a finite dimensional space the quadratic form is therefore the orthogonal sum of
its restrictions to the two subspaces, and its negative index of inertia is the sum of their
negative indices; a vector of the kernel of the orbit sum which is orthogonal to that kernel is
orthogonal to everything. This is the linear algebra of the Hessian of an invariant function at
a fixed point: for the rotation by one period of iterated polygons, the fixed vectors are the
iterated vectors. -/

@[expose] public section

namespace Finsler.SymmetricBlocks

open Module QuadraticForm QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (ρ : V →ₗ[ℝ] V) (k : ℕ)

/-- The sum of the powers ρ^0, …, ρ^(k−1). -/
def powSum : V →ₗ[ℝ] V := ∑ j ∈ Finset.range k, ρ ^ j

/-- The fixed vectors of ρ. -/
def fixed : Submodule ℝ V := LinearMap.ker (ρ - 1)

/-- The vectors with vanishing orbit sum. -/
def normal : Submodule ℝ V := LinearMap.ker (powSum ρ k)

theorem mem_fixed (v : V) : v ∈ fixed ρ ↔ ρ v = v := by
  rw [fixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem mem_normal (v : V) : v ∈ normal ρ k ↔ powSum ρ k v = 0 := LinearMap.mem_ker

theorem powSum_apply (v : V) : powSum ρ k v = ∑ j ∈ Finset.range k, (ρ ^ j) v := by
  rw [powSum, LinearMap.sum_apply]

theorem pow_apply_fixed {v : V} (hv : ρ v = v) (j : ℕ) : (ρ ^ j) v = v := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, Module.End.mul_apply, hv, ih]

theorem powSum_fixed {v : V} (hv : ρ v = v) : powSum ρ k v = (k : ℝ) • v := by
  rw [powSum_apply, Finset.sum_congr rfl fun j _ => pow_apply_fixed ρ hv j, Finset.sum_const,
    Finset.card_range, Nat.cast_smul_eq_nsmul]

variable {ρ k}

/-- The orbit sum of a vector is fixed. -/
theorem map_powSum (hρ : ρ ^ k = 1) (v : V) : ρ (powSum ρ k v) = powSum ρ k v := by
  rw [powSum_apply, map_sum]
  have h1 : ∀ j, ρ ((ρ ^ j) v) = (ρ ^ (j + 1)) v := fun j => by
    rw [pow_succ', Module.End.mul_apply]
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  have h2 := Finset.sum_range_succ (fun j => (ρ ^ j) v) k
  have h3 := Finset.sum_range_succ' (fun j => (ρ ^ j) v) k
  rw [h2] at h3
  have h4 : (ρ ^ k) v = (ρ ^ 0) v := by rw [hρ, pow_zero]
  rw [h4] at h3
  exact (add_right_cancel h3).symm

/-- The fixed vectors and the vectors with vanishing orbit sum are complementary. -/
theorem isCompl (hk : 0 < k) (hρ : ρ ^ k = 1) : IsCompl (fixed ρ) (normal ρ k) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  refine ⟨Submodule.disjoint_def.mpr fun v hv hn => ?_, Submodule.codisjoint_iff_exists_add_eq.mpr
    fun v => ?_⟩
  · have h1 := powSum_fixed ρ k ((mem_fixed ρ v).mp hv)
    rw [(mem_normal ρ k v).mp hn] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left hk0
  · refine ⟨(k : ℝ)⁻¹ • powSum ρ k v, v - (k : ℝ)⁻¹ • powSum ρ k v, ?_, ?_, by abel⟩
    · rw [mem_fixed, map_smul, map_powSum hρ]
    · rw [mem_normal, map_sub, map_smul, powSum_fixed ρ k (map_powSum hρ v), smul_smul,
        inv_mul_cancel₀ hk0, one_smul, sub_self]

variable (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

theorem form_pow (hinv : ∀ v w, β (ρ v) (ρ w) = β v w) (j : ℕ) (v w : V) :
    β ((ρ ^ j) v) ((ρ ^ j) w) = β v w := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hinv, ih]

/-- A fixed vector is orthogonal to every vector with vanishing orbit sum. -/
theorem form_eq_zero (hk : 0 < k) (hinv : ∀ v w, β (ρ v) (ρ w) = β v w) {u w : V}
    (hu : ρ u = u) (hw : powSum ρ k w = 0) : β u w = 0 := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have h1 : β u (powSum ρ k w) = (k : ℝ) * β u w := by
    rw [powSum_apply, map_sum]
    have h2 : ∀ j ∈ Finset.range k, β u ((ρ ^ j) w) = β u w := fun j _ => by
      have h3 := form_pow β hinv j u w
      rwa [pow_apply_fixed ρ hu j] at h3
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hw, map_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hk0

variable {β}

/-- The quadratic form splits along the fixed vectors and the vectors with vanishing orbit
sum. -/
theorem quad_add (hk : 0 < k) (hsym : ∀ v w, β v w = β w v)
    (hinv : ∀ v w, β (ρ v) (ρ w) = β v w) {u w : V} (hu : u ∈ fixed ρ) (hw : w ∈ normal ρ k) :
    LinearMap.BilinMap.toQuadraticMap β (u + w) =
      LinearMap.BilinMap.toQuadraticMap β u + LinearMap.BilinMap.toQuadraticMap β w := by
  have h1 := form_eq_zero β hk hinv ((mem_fixed ρ u).mp hu) ((mem_normal ρ k w).mp hw)
  have h2 : β w u = 0 := by rw [hsym]; exact h1
  change β (u + w) (u + w) = β u u + β w w
  simp only [map_add, LinearMap.add_apply, h1, h2]
  ring

variable [FiniteDimensional ℝ V]

/-- The negative index of inertia is the sum of the negative indices on the fixed vectors and
on the vectors with vanishing orbit sum. -/
theorem sigNeg_eq_add (hk : 0 < k) (hρ : ρ ^ k = 1) (hsym : ∀ v w, β v w = β w v)
    (hinv : ∀ v w, β (ρ v) (ρ w) = β v w) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap β) =
      sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed ρ)) +
        sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (normal ρ k)) := by
  have hc := isCompl hk hρ
  have hequiv : QuadraticMap.Equivalent
      (((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed ρ)).prod
        ((LinearMap.BilinMap.toQuadraticMap β).restrict (normal ρ k)))
      (LinearMap.BilinMap.toQuadraticMap β) :=
    ⟨⟨Submodule.prodEquivOfIsCompl (fixed ρ) (normal ρ k) hc, fun x => by
      change LinearMap.BilinMap.toQuadraticMap β
        (Submodule.prodEquivOfIsCompl (fixed ρ) (normal ρ k) hc x) = _
      rw [Submodule.coe_prodEquivOfIsCompl', quad_add hk hsym hinv x.1.2 x.2.2,
        QuadraticMap.prod_apply, restrict_apply, restrict_apply]⟩⟩
  rw [← hequiv.sigNeg_eq, QuadraticForm.sigNeg_prod]

omit [FiniteDimensional ℝ V] in
/-- A vector with vanishing orbit sum which is orthogonal to all such vectors is orthogonal to
every vector. -/
theorem form_eq_zero_of_normal (hk : 0 < k) (hρ : ρ ^ k = 1) (hsym : ∀ v w, β v w = β w v)
    (hinv : ∀ v w, β (ρ v) (ρ w) = β v w) {v : V} (hv : v ∈ normal ρ k)
    (h : ∀ w ∈ normal ρ k, β v w = 0) (x : V) : β v x = 0 := by
  obtain ⟨u, w, hu, hw, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp (isCompl hk hρ).2 x
  rw [map_add, h w hw, add_zero, hsym]
  exact form_eq_zero β hk hinv ((mem_fixed ρ u).mp hu) ((mem_normal ρ k v).mp hv)

end

end Finsler.SymmetricBlocks
