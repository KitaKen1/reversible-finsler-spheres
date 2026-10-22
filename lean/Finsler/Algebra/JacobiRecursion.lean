module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Propagation along a closed chain. A family of vectors indexed by the residues modulo N
which vanishes at two consecutive indices and has the propagation property (if it vanishes at
j - 1 and j, it vanishes at j + 1) is zero. Hence a linear operator on the L² product of N
copies of a finite-dimensional space V, all of whose kernel vectors have the propagation
property, has nullity at most 2 dim V: a kernel vector is determined by its components at the
indices 0 and 1. This is the linear part of the bound for the nullity of the Hessian of a
nearest-neighbour energy (discrete Jacobi fields). -/

@[expose] public section

namespace Finsler.JacobiRecursion

open Module

variable {V : Type*} {N : ℕ} [NeZero N]

/-- A family vanishing at two consecutive indices with the propagation property is zero. -/
theorem eq_zero_of_propagation [Zero V] (w : ZMod N → V) (h0 : w 0 = 0) (h1 : w 1 = 0)
    (hprop : ∀ j : ZMod N, w (j - 1) = 0 → w j = 0 → w (j + 1) = 0) (i : ZMod N) : w i = 0 := by
  have key : ∀ k : ℕ, w (k : ZMod N) = 0 ∧ w ((k : ZMod N) + 1) = 0 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_add]
      exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨by rw [Nat.cast_succ]; exact ih.2, ?_⟩
      have h := hprop ((k : ZMod N) + 1) (by rw [add_sub_cancel_right]; exact ih.1) ih.2
      rw [Nat.cast_succ]
      exact h
  have h := (key i.val).1
  rwa [ZMod.natCast_zmod_val] at h

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The nullity of an operator on a closed chain whose kernel vectors have the propagation
property is at most twice the dimension of the vertex space. -/
theorem finrank_ker_le
    (H : PiLp 2 (fun _ : ZMod N => V) →ₗ[ℝ] PiLp 2 (fun _ : ZMod N => V))
    (hprop : ∀ w, H w = 0 → ∀ j : ZMod N, w (j - 1) = 0 → w j = 0 → w (j + 1) = 0) :
    finrank ℝ (LinearMap.ker H) ≤ 2 * finrank ℝ V := by
  set φ : LinearMap.ker H →ₗ[ℝ] V × V :=
    { toFun := fun w => ((w : PiLp 2 (fun _ : ZMod N => V)) 0, (w : PiLp 2 (fun _ : ZMod N => V)) 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h0 : (w : PiLp 2 (fun _ : ZMod N => V)) 0 = 0 := congrArg Prod.fst hw
    have h1 : (w : PiLp 2 (fun _ : ZMod N => V)) 1 = 0 := congrArg Prod.snd hw
    apply Subtype.ext
    refine PiLp.ext fun i => ?_
    exact eq_zero_of_propagation (fun i => (w : PiLp 2 (fun _ : ZMod N => V)) i) h0 h1
      (hprop w (LinearMap.mem_ker.mp w.2)) i
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_prod] at h
  omega

end Finsler.JacobiRecursion
