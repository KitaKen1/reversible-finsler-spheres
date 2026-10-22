module

public import Finsler.Topology.BorelQuasiIso
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Dimension count in the Gysin sequence of an involutive complex. In the exact sequence
⋯ → HR^{q-1} → HR^q → H^q → HR^q → HR^{q+1} → ⋯ (multiplication by w, forgetting the action,
transfer), the kernel of the transfer is the image of the forgetful map, the image of the
transfer is the kernel of w, and the kernel of the forgetful map is the image of w. If all
groups are finite dimensional, rank–nullity gives for every Q

  Σ_{q ≤ Q} dim H^q + dim ker(w on HR^Q) = dim HR^Q + 2 Σ_{q ≤ Q} dim ker(w on HR^q).

If ordinary cohomology vanishes from degree Q₁ on, then w is injective on HR^q for q ≥ Q₁, the
dimension of HR^q does not depend on q ≥ Q₁, and the total dimension of ordinary cohomology is
this stable dimension plus twice the total dimension of the kernel of w. -/

@[expose] public section

namespace Finsler.GysinCount

open Finsler.BorelCochain Module

noncomputable section

variable (K : InvComplex)

theorem ker_transfer (q : ℕ) : LinearMap.ker (transfer K q) = LinearMap.range (forget K q) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  exact exact_transfer K q z

theorem range_transfer (q : ℕ) : LinearMap.range (transfer K q) = LinearMap.ker (w K q) := by
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  exact (exact_w K q y).symm

theorem ker_forget (q : ℕ) : LinearMap.ker (forget K (q + 1)) = LinearMap.range (w K q) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  exact exact_forget K q x

section Finite

/-- dim H^q = dim im(forget on HR^q) + dim ker(w on HR^q). -/
theorem finrank_H (q : ℕ) [Module.Finite (ZMod 2) (H K q)] : finrank (ZMod 2) (H K q) =
    finrank (ZMod 2) (LinearMap.range (forget K q)) +
      finrank (ZMod 2) (LinearMap.ker (w K q)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (transfer K q)
  rw [ker_transfer, range_transfer] at h
  omega

/-- dim HR^q = dim ker(w on HR^q) + dim im(w on HR^q). -/
theorem finrank_HR (q : ℕ) [Module.Finite (ZMod 2) (HR K q)] : finrank (ZMod 2) (HR K q) =
    finrank (ZMod 2) (LinearMap.ker (w K q)) + finrank (ZMod 2) (LinearMap.range (w K q)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (w K q)
  omega

/-- dim HR^{q+1} = dim im(w on HR^q) + dim im(forget on HR^{q+1}). -/
theorem finrank_HR_succ (q : ℕ) [Module.Finite (ZMod 2) (HR K (q + 1))] :
    finrank (ZMod 2) (HR K (q + 1)) =
    finrank (ZMod 2) (LinearMap.range (w K q)) +
      finrank (ZMod 2) (LinearMap.range (forget K (q + 1))) := by
  have h := LinearMap.finrank_range_add_finrank_ker (forget K (q + 1))
  rw [ker_forget] at h
  omega

theorem finrank_HR_zero :
    finrank (ZMod 2) (HR K 0) = finrank (ZMod 2) (LinearMap.range (forget K 0)) :=
  (LinearMap.finrank_range_of_inj (BorelQuasiIso.forget_zero_injective K)).symm

variable [∀ q, Module.Finite (ZMod 2) (H K q)] [∀ q, Module.Finite (ZMod 2) (HR K q)]

/-- The dimension count of the Gysin sequence up to degree Q. -/
theorem gysin_count (Q : ℕ) :
    ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (H K q) +
        finrank (ZMod 2) (LinearMap.ker (w K Q)) =
      finrank (ZMod 2) (HR K Q) +
        2 * ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (LinearMap.ker (w K q)) := by
  induction Q with
  | zero =>
    have h1 := finrank_H K 0
    have h2 := finrank_HR_zero K
    rw [Finset.sum_range_one, Finset.sum_range_one]
    omega
  | succ Q ih =>
    rw [Finset.sum_range_succ,
      Finset.sum_range_succ (fun q => finrank (ZMod 2) (LinearMap.ker (w K q)))]
    have h1 := finrank_H K (Q + 1)
    have h2 := finrank_HR K Q
    have h3 := finrank_HR_succ K Q
    omega

end Finite

section Vanishing

variable {K} {Q₁ : ℕ} (hzero : ∀ q, Q₁ ≤ q → ∀ z : H K q, z = 0)

include hzero in
/-- Where ordinary cohomology vanishes, w is injective. -/
theorem ker_w_eq_bot (q : ℕ) (hq : Q₁ ≤ q) : LinearMap.ker (w K q) = ⊥ := by
  rw [← range_transfer, eq_bot_iff]
  rintro _ ⟨z, rfl⟩
  rw [hzero q hq z, map_zero]
  exact Submodule.zero_mem _

include hzero in
/-- Where ordinary cohomology vanishes in the target degree, w is surjective. -/
theorem range_w_eq_top (q : ℕ) (hq : Q₁ ≤ q + 1) : LinearMap.range (w K q) = ⊤ := by
  rw [← ker_forget, eq_top_iff]
  intro x _
  exact hzero (q + 1) hq (forget K (q + 1) x)

include hzero in
/-- Above the degrees of ordinary cohomology the dimension of HR does not depend on the
degree. -/
theorem finrank_HR_stable (q : ℕ) (hq : Q₁ ≤ q) :
    finrank (ZMod 2) (HR K q) = finrank (ZMod 2) (HR K Q₁) := by
  induction q, hq using Nat.le_induction with
  | base => rfl
  | succ q hq ih =>
    rw [← ih]
    have e : HR K q ≃ₗ[ZMod 2] HR K (q + 1) :=
      LinearEquiv.ofBijective (w K q)
        ⟨LinearMap.ker_eq_bot.mp (ker_w_eq_bot hzero q hq),
          LinearMap.range_eq_top.mp (range_w_eq_top hzero q (by omega))⟩
    exact e.finrank_eq.symm

variable [∀ q, Module.Finite (ZMod 2) (H K q)] [∀ q, Module.Finite (ZMod 2) (HR K q)]

include hzero in
/-- If ordinary cohomology vanishes from degree Q₁ on, its total dimension is the stable
dimension of HR plus twice the total dimension of the kernel of w. -/
theorem total_count (Q : ℕ) (hQ : Q₁ ≤ Q) :
    ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (H K q) =
      finrank (ZMod 2) (HR K Q) +
        2 * ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (LinearMap.ker (w K q)) := by
  have h := gysin_count K Q
  have hk : finrank (ZMod 2) (LinearMap.ker (w K Q)) = 0 := by
    rw [ker_w_eq_bot hzero Q hQ]
    exact finrank_bot (ZMod 2) (HR K Q)
  omega

end Vanishing

end

end Finsler.GysinCount
