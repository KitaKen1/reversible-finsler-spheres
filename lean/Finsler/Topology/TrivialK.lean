module

public import Finsler.Topology.NilpotentWK
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Iterated Borel cohomology for a trivial second involution. If the second involution acts as
the identity on cochains, the iterated Borel complex has the trivial involution, and a class of
degree n has components in the reflection Borel cohomology of every degree j ≤ n, which
determine it. The reflection class shifts the components by one degree and acts on them as w.
Hence a power of w vanishing on reflection Borel cohomology vanishes, as a power of the
reflection class, on the iterated Borel cohomology; and the iterated Borel cohomology of degree
J is the product of the reflection Borel cohomology groups of degrees at most J, so its
dimension is the sum of their dimensions. -/

@[expose] public section

namespace Finsler.TrivialK

open Finsler.BorelCochain Finsler.BorelIterate Finsler.BorelGraded Finsler.BorelFreeK
open Finsler.NilpotentW Finsler.NilpotentWK

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : InvComplex} (S : Commuting K) (hS : ∀ j x, S.s j x = x)

include hS in
/-- If the second involution is the identity, the iterated Borel complex has the trivial
involution. -/
theorem borelInv_trivial (n : ℕ) (x : (borelInv S).C n) : (borelInv S).t n x = x := by
  apply Subtype.ext
  funext j
  exact hS j _

/-- The component of degree j of an iterated Borel class, in reflection Borel cohomology. -/
def theta (n j : ℕ) : HR (borelInv S) n →ₗ[ZMod 2] HR K j :=
  (cohomologyEquiv S j).toLinearMap ∘ₗ comp (borelInv S) (borelInv_trivial S hS) n j

theorem theta_mk (n j : ℕ) (c : bcocycles (borelInv S) n) :
    theta S hS n j (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (cocycleEquiv S j (compCocycle (borelInv S) (borelInv_trivial S hS) n j c)) := rfl

/-- The components of degree at most n determine a class of degree n. -/
theorem eq_zero_of_theta (n : ℕ) (x : HR (borelInv S) n)
    (hx : ∀ j, j ≤ n → theta S hS n j x = 0) : x = 0 := by
  apply split_injective (borelInv S) (borelInv_trivial S hS) n
  rw [map_zero]
  funext j
  apply (cohomologyEquiv S j).injective
  change cohomologyEquiv S j (comp (borelInv S) (borelInv_trivial S hS) n j x) =
    cohomologyEquiv S j 0
  rw [map_zero]
  exact hx j (Nat.lt_succ_iff.mp j.2)

theorem total_innerW_mem (n : ℕ) (c : bcocycles (borelInv S) n) :
    total (innerW S) (c : Seq (borelInv S)) ∈ bcocycles (borelInv S) (n + 1) := by
  have h : total (innerW S) (c : Seq (borelInv S)) ∈ bcocycles (borelInv S) (1 + n) :=
    (cyclesMap (innerW S) n c).2
  rwa [Nat.add_comm 1 n] at h

/-- The reflection class on a representative. -/
theorem innerStep_mk (n : ℕ) (c : bcocycles (borelInv S) n) :
    innerStep S n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (⟨total (innerW S) (c : Seq (borelInv S)), total_innerW_mem S n c⟩ :
        bcocycles (borelInv S) (n + 1)) := by
  rw [innerStep_apply, onHR_mk]
  exact castHR_mk (Nat.add_comm 1 n) (total (innerW S) (c : Seq (borelInv S)))
    (cyclesMap (innerW S) n c).2 (total_innerW_mem S n c)

/-- The reflection class shifts the components and acts on them as w. -/
theorem theta_innerStep_succ (n j : ℕ) (x : HR (borelInv S) n) :
    theta S hS (n + 1) (j + 1) (innerStep S n x) = w K j (theta S hS n j x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have e : seqOf S (j + 1) (total (innerW S) (c : Seq (borelInv S)) (j + 1)) =
      seqOf S j ((c : Seq (borelInv S)) j) := by
    rw [cast_seq (Nat.add_comm 1 j) (total (innerW S) (c : Seq (borelInv S))), seqOf_castC,
      total_at]
    rfl
  rw [innerStep_mk, theta_mk, theta_mk]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk (Submodule.inclusion
    (bcocycles_mono K j)
    (cocycleEquiv S j (compCocycle (borelInv S) (borelInv_trivial S hS) n j c)))
  exact congrArg Submodule.Quotient.mk (Subtype.ext e)

/-- The component of degree zero of the image of the reflection class vanishes. -/
theorem theta_innerStep_zero (n : ℕ) (x : HR (borelInv S) n) :
    theta S hS (n + 1) 0 (innerStep S n x) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have e : seqOf S 0 (total (innerW S) (c : Seq (borelInv S)) 0) = 0 := by
    rw [total_below (innerW S) _ (by omega : 0 < 1)]
    rfl
  have h0 : cocycleEquiv S 0 (compCocycle (borelInv S) (borelInv_trivial S hS) (n + 1) 0
      ⟨total (innerW S) (c : Seq (borelInv S)), total_innerW_mem S n c⟩) = 0 := Subtype.ext e
  rw [innerStep_mk, theta_mk, h0, Submodule.Quotient.mk_zero]

/-- The components of low degree of a power of the reflection class vanish. -/
theorem theta_innerPow_low (lo : ℕ) (x : HR (borelInv S) lo) (k : ℕ) :
    ∀ j, j < k → theta S hS (lo + k) j (innerPow S lo k x) = 0 := by
  induction k with
  | zero => exact fun j hj => absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro j hj
    cases j with
    | zero => exact theta_innerStep_zero S hS (lo + k) (innerPow S lo k x)
    | succ j =>
      change theta S hS (lo + k + 1) (j + 1) (innerStep S (lo + k) (innerPow S lo k x)) = 0
      rw [theta_innerStep_succ, ih j (by omega), map_zero]

/-- The other components of a power of the reflection class are the powers of w of the
components. -/
theorem theta_innerPow (lo j : ℕ) (x : HR (borelInv S) lo) (k : ℕ) :
    theta S hS (lo + k) (j + k) (innerPow S lo k x) = wPow K j k (theta S hS lo j x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change theta S hS (lo + k + 1) (j + k + 1) (innerStep S (lo + k) (innerPow S lo k x)) =
      w K (j + k) (wPow K j k (theta S hS lo j x))
    rw [theta_innerStep_succ, ih]

include hS in
/-- For a trivial second involution, a power of w vanishing on reflection Borel cohomology
vanishes as a power of the reflection class on the iterated Borel cohomology. -/
theorem innerPow_eq_zero_of_trivial {M : ℕ}
    (hw : ∀ (lo : ℕ) (x : HR K lo), wPow K lo M x = 0) (lo : ℕ) (x : HR (borelInv S) lo) :
    innerPow S lo M x = 0 := by
  apply eq_zero_of_theta S hS (lo + M)
  intro j _
  by_cases hj : j < M
  · exact theta_innerPow_low S hS lo x M j hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + M := ⟨j - M, by omega⟩
    rw [theta_innerPow, hw]

/-- For a trivial second involution the iterated Borel cohomology of degree J is the product of
the reflection Borel cohomology groups of degrees at most J. -/
def trivSplit (J : ℕ) : HR (borelInv S) J ≃ₗ[ZMod 2] ((l : Fin (J + 1)) → HR K l) :=
  (splitEquiv (borelInv S) (borelInv_trivial S hS) J).trans
    (LinearEquiv.piCongrRight fun l => cohomologyEquiv S l)

include hS in
/-- The dimension formula for a trivial second involution. -/
theorem finrank_trivial [∀ l, Module.Finite (ZMod 2) (HR K l)] (J : ℕ) :
    Module.finrank (ZMod 2) (HR (borelInv S) J) =
      ∑ l ∈ Finset.range (J + 1), Module.finrank (ZMod 2) (HR K l) := by
  have hfree : ∀ i : Fin (J + 1), Module.Free (ZMod 2) (HR K i) := fun i =>
    Module.Free.of_divisionRing (ZMod 2) (HR K i)
  rw [(trivSplit S hS J).finrank_eq, Module.finrank_pi_fintype,
    Fin.sum_univ_eq_sum_range (fun l => Module.finrank (ZMod 2) (HR K l)) (J + 1)]

include hS in
/-- If the reflection Borel cohomology is finite dimensional in every degree, so is the iterated
Borel cohomology for a trivial second involution. -/
theorem finite_trivial [∀ l, Module.Finite (ZMod 2) (HR K l)] (J : ℕ) :
    Module.Finite (ZMod 2) (HR (borelInv S) J) :=
  Module.Finite.equiv (trivSplit S hS J).symm

end

end Finsler.TrivialK
