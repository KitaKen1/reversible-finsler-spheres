module

public import Finsler.Algebra.SymmetricBlocks

/-! A cyclic root/normal splitting remains an orthogonal splitting on the fixed space
of any commuting linear map. This bounds the fixed normal index using the full fixed
index and the ordinary root index. -/

@[expose] public section

namespace Finsler.CommutingFixedIndex

open Module QuadraticMap QuadraticForm Finsler.SymmetricBlocks

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (ρ T : Module.End ℝ V) (k : ℕ) (hcomm : ∀ v, T (ρ v) = ρ (T v))

include hcomm in
private theorem pow_commute (j : ℕ) (v : V) : T ((ρ ^ j) v) = (ρ ^ j) (T v) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hcomm, ih]

include hcomm in
theorem powSum_commute (v : V) : T (powSum ρ k v) = powSum ρ k (T v) := by
  rw [powSum_apply, map_sum, powSum_apply]
  exact Finset.sum_congr rfl fun j _ => pow_commute ρ T hcomm j v

def addFixed : (↥(fixed ρ ⊓ fixed T) × ↥(normal ρ k ⊓ fixed T)) →ₗ[ℝ] fixed T :=
  (Submodule.inclusion (show fixed ρ ⊓ fixed T ≤ fixed T from inf_le_right)).coprod
    (Submodule.inclusion (show normal ρ k ⊓ fixed T ≤ fixed T from inf_le_right))

include hcomm in
theorem bijective_addFixed (hk : 0 < k) (hρ : ρ ^ k = 1) :
    Function.Bijective (addFixed ρ T k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hsum : (x.1 : V) + (x.2 : V) = 0 := congrArg Subtype.val hx
    have hu : (x.1 : V) = -(x.2 : V) := eq_neg_of_add_eq_zero_left hsum
    have hun : (x.1 : V) ∈ normal ρ k := by
      rw [hu]
      exact (normal ρ k).neg_mem x.2.2.1
    have hz := Submodule.disjoint_def.mp (Finsler.SymmetricBlocks.isCompl hk hρ).1
      x.1 x.1.2.1 hun
    rw [hz, zero_add] at hsum
    exact Prod.ext (Subtype.ext hz) (Subtype.ext hsum)
  · intro v
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    let u : V := (k : ℝ)⁻¹ • powSum ρ k v
    have huρ : u ∈ fixed ρ := by
      rw [mem_fixed, map_smul, map_powSum hρ]
    have huT : u ∈ fixed T := by
      rw [mem_fixed, map_smul, powSum_commute ρ T k hcomm,
        (mem_fixed T (v : V)).mp v.2]
    have hwρ : (v : V) - u ∈ normal ρ k := by
      rw [mem_normal, map_sub]
      change powSum ρ k (v : V) - powSum ρ k ((k : ℝ)⁻¹ • powSum ρ k v) = 0
      rw [map_smul, powSum_fixed ρ k (map_powSum hρ v), smul_smul,
        inv_mul_cancel₀ hk0, one_smul, sub_self]
    refine ⟨(⟨u, huρ, huT⟩, ⟨(v : V) - u, hwρ, (fixed T).sub_mem v.2 huT⟩), ?_⟩
    apply Subtype.ext
    change u + ((v : V) - u) = (v : V)
    abel

def splitFixedEquiv (hk : 0 < k) (hρ : ρ ^ k = 1) :
    (↥(fixed ρ ⊓ fixed T) × ↥(normal ρ k ⊓ fixed T)) ≃ₗ[ℝ] fixed T :=
  LinearEquiv.ofBijective (addFixed ρ T k) (bijective_addFixed ρ T k hcomm hk hρ)

variable [FiniteDimensional ℝ V]

theorem sigNeg_restrict_mono (Q : QuadraticForm ℝ V) {A B : Submodule ℝ V} (h : A ≤ B) :
    sigNeg (Q.restrict A) ≤ sigNeg (Q.restrict B) := by
  have he : QuadraticMap.Equivalent
      ((Q.restrict B).restrict (A.comap B.subtype)) (Q.restrict A) :=
    ⟨⟨Submodule.comapSubtypeEquivOfLe h, fun _ => rfl⟩⟩
  rw [← he.sigNeg_eq]
  exact QuadraticForm.sigNeg_restrict_le (Q.restrict B) (A.comap B.subtype)

include hcomm in
theorem sigNeg_fixed_eq_add (hk : 0 < k) (hρ : ρ ^ k = 1)
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ v w, β v w = β w v)
    (hinv : ∀ v w, β (ρ v) (ρ w) = β v w) :
    sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed T)) =
      sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed ρ ⊓ fixed T)) +
        sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (normal ρ k ⊓ fixed T)) := by
  have he : QuadraticMap.Equivalent
      (((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed ρ ⊓ fixed T)).prod
        ((LinearMap.BilinMap.toQuadraticMap β).restrict (normal ρ k ⊓ fixed T)))
      ((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed T)) :=
    ⟨⟨splitFixedEquiv ρ T k hcomm hk hρ, fun x => by
      change LinearMap.BilinMap.toQuadraticMap β ((x.1 : V) + (x.2 : V)) =
        LinearMap.BilinMap.toQuadraticMap β (x.1 : V) +
          LinearMap.BilinMap.toQuadraticMap β (x.2 : V)
      exact Finsler.SymmetricBlocks.quad_add hk hsym hinv x.1.2.1 x.2.2.1⟩⟩
  rw [← he.sigNeg_eq, QuadraticForm.sigNeg_prod]

include hcomm in
theorem sigNeg_fixed_bounds (hk : 0 < k) (hρ : ρ ^ k = 1)
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ v w, β v w = β w v)
    (hinv : ∀ v w, β (ρ v) (ρ w) = β v w) :
    sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (normal ρ k ⊓ fixed T)) ≤
        sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed T)) ∧
      sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed T)) ≤
        sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (fixed ρ)) +
          sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict (normal ρ k ⊓ fixed T)) := by
  have h := sigNeg_fixed_eq_add ρ T k hcomm hk hρ β hsym hinv
  have hr := sigNeg_restrict_mono (LinearMap.BilinMap.toQuadraticMap β)
    (show fixed ρ ⊓ fixed T ≤ fixed ρ from inf_le_left)
  omega

end

end Finsler.CommutingFixedIndex
