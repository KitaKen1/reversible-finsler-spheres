module

public import Finsler.Topology.BorelCoverK
public import Finsler.Topology.NilpotentWK
public import Mathlib.Algebra.Ring.GeomSum

/-! Nilpotence of v from nilpotence of w and of U = v(v + w). A family of degree-one maps of a
graded module is an endomorphism of the product of the graded pieces; its k-th power is the
k-fold composite in each degree. In a ring, if V and W commute, W^M = 0 and (V(V + W))^k = 0,
then V^{(M+1)k} = 0, because V^M = (V + W)·Q for a polynomial Q in V and W. Hence, for two
commuting families f and g of degree-one maps, if the M-fold composites of g vanish and the
k-th power of f(f + g) annihilates every class, the (M+1)k-fold composites of f vanish. On the
Borel cohomology of an iterated complex the class v of the second involution commutes with the
reflection class w; so if the M-th power of w and the k-th power of U = v(v + w) vanish, the
(M+1)k-th power of v vanishes. -/

@[expose] public section

namespace Finsler.OperatorK

open Finsler.BorelCochain Finsler.BorelIterate Finsler.BorelGraded Finsler.BorelFreeK
open Finsler.BorelCoverK Finsler.NilpotentWK

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### A polynomial identity -/

/-- In a ring, if V and W commute, W^M = 0 and (V(V + W))^k = 0, then V^{(M+1)k} = 0. -/
theorem pow_eq_zero_of_commute {R : Type*} [Ring R] {V W : R} (hc : Commute V W) {M k : ℕ}
    (hW : W ^ M = 0) (hU : (V * (V + W)) ^ k = 0) : V ^ ((M + 1) * k) = 0 := by
  have hc' : Commute V (-W) := hc.neg_right
  have hgeom := hc'.mul_geom_sum₂ M
  rw [sub_neg_eq_add, neg_pow, hW, mul_zero, sub_zero] at hgeom
  have hVQ : Commute V (∑ i ∈ Finset.range M, V ^ i * (-W) ^ (M - 1 - i)) :=
    Commute.sum_right _ _ _ fun i _ =>
      ((Commute.refl V).pow_right i).mul_right (hc'.pow_right _)
  have hWQ : Commute W (∑ i ∈ Finset.range M, V ^ i * (-W) ^ (M - 1 - i)) :=
    Commute.sum_right _ _ _ fun i _ =>
      (hc.symm.pow_right i).mul_right ((Commute.refl W).neg_right.pow_right _)
  have hUQ : Commute (V * (V + W)) (∑ i ∈ Finset.range M, V ^ i * (-W) ^ (M - 1 - i)) :=
    hVQ.mul_left (hVQ.add_left hWQ)
  have h1 : V ^ (M + 1) =
      V * (V + W) * ∑ i ∈ Finset.range M, V ^ i * (-W) ^ (M - 1 - i) := by
    rw [pow_succ', ← hgeom, mul_assoc]
  rw [pow_mul, h1, hUQ.mul_pow, hU, zero_mul]

/-! ### Degree-one operators on the product of the graded pieces -/

section Shift

variable (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]

/-- A family of degree-one maps as an endomorphism of the product of the graded pieces. -/
def shiftOp (f : ∀ q, G q →ₗ[ZMod 2] G (q + 1)) :
    Module.End (ZMod 2) ((q : ℕ) → G q) where
  toFun x j := Nat.casesOn (motive := G) j 0 fun q => f q (x q)
  map_add' x y := by
    funext j
    cases j with
    | zero => exact (add_zero (0 : G 0)).symm
    | succ q => exact map_add (f q) (x q) (y q)
  map_smul' c x := by
    funext j
    cases j with
    | zero => exact (smul_zero c).symm
    | succ q => exact map_smul (f q) c (x q)

variable {G} (f g : ∀ q, G q →ₗ[ZMod 2] G (q + 1))

theorem shiftOp_zero (x : (q : ℕ) → G q) : shiftOp G f x 0 = 0 := rfl

theorem shiftOp_succ (x : (q : ℕ) → G q) (q : ℕ) : shiftOp G f x (q + 1) = f q (x q) := rfl

/-- Families which commute degreewise give commuting endomorphisms. -/
theorem shiftOp_commute (h : ∀ q x, f (q + 1) (g q x) = g (q + 1) (f q x)) :
    Commute (shiftOp G f) (shiftOp G g) := by
  change shiftOp G f * shiftOp G g = shiftOp G g * shiftOp G f
  apply LinearMap.ext
  intro x
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero =>
      change f 0 (shiftOp G g x 0) = g 0 (shiftOp G f x 0)
      rw [shiftOp_zero, shiftOp_zero, map_zero, map_zero]
    | succ q => exact h q (x q)

/-- The k-th power of the endomorphism is the k-fold composite in each degree. -/
theorem shiftOp_pow_apply (k lo : ℕ) (x : (q : ℕ) → G q) :
    (shiftOp G f ^ k) x (lo + k) =
      Finsler.Gysin.word (V := fun i => G (lo + i)) (fun i => (f (lo + i)).toAddMonoidHom) k
        (x lo) := by
  induction k with
  | zero =>
    rw [pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ']
    change f (lo + k) ((shiftOp G f ^ k) x (lo + k)) = _
    rw [ih]
    rfl

theorem shiftOp_pow_low (k : ℕ) : ∀ (j : ℕ) (_ : j < k) (x : (q : ℕ) → G q),
    (shiftOp G f ^ k) x j = 0 := by
  induction k with
  | zero => exact fun j hj => absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro j hj x
    rw [pow_succ']
    cases j with
    | zero => rfl
    | succ j =>
      change f j ((shiftOp G f ^ k) x j) = 0
      rw [ih j (by omega) x, map_zero]

/-- If the k-fold composites vanish, the k-th power of the endomorphism vanishes. -/
theorem shiftOp_pow_eq_zero (k : ℕ)
    (h : ∀ (lo : ℕ) (x : G lo), Finsler.Gysin.word (V := fun i => G (lo + i))
      (fun i => (f (lo + i)).toAddMonoidHom) k x = 0) : shiftOp G f ^ k = 0 := by
  apply LinearMap.ext
  intro x
  funext j
  by_cases hj : j < k
  · exact shiftOp_pow_low f k j hj x
  · obtain ⟨lo, rfl⟩ : ∃ lo, j = lo + k := ⟨j - k, by omega⟩
    rw [shiftOp_pow_apply]
    exact h lo (x lo)

/-- If the k-th power of the endomorphism vanishes, the k-fold composites vanish. -/
theorem word_eq_zero_of_pow (k : ℕ) (h : shiftOp G f ^ k = 0) (lo : ℕ) (x : G lo) :
    Finsler.Gysin.word (V := fun i => G (lo + i)) (fun i => (f (lo + i)).toAddMonoidHom) k
      x = 0 := by
  have h1 := shiftOp_pow_apply f k lo (Pi.single lo x)
  rw [h, Pi.single_eq_same] at h1
  exact h1.symm

/-- The class x is annihilated by the k-th power of f(f + g). -/
def AnnG : ℕ → (q : ℕ) → G q → Prop
  | 0, _, x => x = 0
  | k + 1, q, x => AnnG k (q + 1 + 1) (f (q + 1) (f q x + g q x))

theorem annG_zero (k : ℕ) : ∀ q : ℕ, AnnG f g k q 0 := by
  induction k with
  | zero => exact fun _ => rfl
  | succ k ih =>
    intro q
    change AnnG f g k (q + 1 + 1) (f (q + 1) (f q 0 + g q 0))
    rw [map_zero, map_zero, add_zero, map_zero]
    exact ih (q + 1 + 1)

/-- If the k-th power of f(f + g) annihilates every class, the k-th power of the endomorphism
f(f + g) of the product vanishes. -/
theorem shiftOp_U_pow_eq_zero (k : ℕ) (h : ∀ (q : ℕ) (x : G q), AnnG f g k q x) :
    (shiftOp G f * (shiftOp G f + shiftOp G g)) ^ k = 0 := by
  have key : ∀ (k : ℕ) (y : (q : ℕ) → G q), (∀ q, AnnG f g k q (y q)) →
      ((shiftOp G f * (shiftOp G f + shiftOp G g)) ^ k) y = 0 := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [pow_zero]
      funext q
      exact hy q
    | succ k ih =>
      intro y hy
      rw [pow_succ]
      refine ih ((shiftOp G f * (shiftOp G f + shiftOp G g)) y) fun j => ?_
      cases j with
      | zero => exact annG_zero f g k 0
      | succ j =>
        cases j with
        | zero =>
          have h0 : (shiftOp G f * (shiftOp G f + shiftOp G g)) y 1 = 0 := by
            change f 0 (shiftOp G f y 0 + shiftOp G g y 0) = 0
            rw [shiftOp_zero, shiftOp_zero, add_zero, map_zero]
          rw [h0]
          exact annG_zero f g k 1
        | succ q => exact hy q
  apply LinearMap.ext
  intro y
  exact key k y fun q => h q (y q)

/-- If f and g commute, the M-fold composites of g vanish and the k-th power of f(f + g)
annihilates every class, the (M+1)k-fold composites of f vanish. -/
theorem word_nilpotent (hcomm : ∀ q x, f (q + 1) (g q x) = g (q + 1) (f q x)) {M k : ℕ}
    (hg : ∀ (lo : ℕ) (x : G lo), Finsler.Gysin.word (V := fun i => G (lo + i))
      (fun i => (g (lo + i)).toAddMonoidHom) M x = 0)
    (hU : ∀ (q : ℕ) (x : G q), AnnG f g k q x) (lo : ℕ) (x : G lo) :
    Finsler.Gysin.word (V := fun i => G (lo + i)) (fun i => (f (lo + i)).toAddMonoidHom)
      ((M + 1) * k) x = 0 :=
  word_eq_zero_of_pow f ((M + 1) * k)
    (pow_eq_zero_of_commute (shiftOp_commute f g hcomm) (shiftOp_pow_eq_zero g M hg)
      (shiftOp_U_pow_eq_zero f g k hU)) lo x

end Shift

/-! ### The two classes on iterated Borel cohomology -/

section Classes

variable {K : InvComplex} (S : Commuting K)

theorem w_castHR {L : InvComplex} {a b : ℕ} (h : a = b) (x : HR L a) :
    w L b (castHR h x) = castHR (congrArg (· + 1) h) (w L a x) := by
  subst b
  rfl

theorem castHR_castHR {L : InvComplex} {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : HR L a) :
    castHR h₂ (castHR h₁ x) = castHR (h₁.trans h₂) x := by
  subst b
  subst c
  rfl

/-- The class of the second involution commutes with the reflection class. -/
theorem w_innerStep (q : ℕ) (x : HR (borelInv S) q) :
    w (borelInv S) (q + 1) (innerStep S q x) = innerStep S (q + 1) (w (borelInv S) q x) := by
  rw [innerStep_apply, innerStep_apply, w_castHR, ← onHR_w (innerW S) q x, castHR_castHR]

/-- The annihilation predicate of U in the generic form. -/
theorem annG_of_ann (k : ℕ) : ∀ (q : ℕ) (x : HR (borelInv S) q), Ann S k q x →
    AnnG (G := fun q => HR (borelInv S) q) (fun q => w (borelInv S) q)
      (fun q => innerStep S q) k q x := by
  induction k with
  | zero => exact fun _ _ h => h
  | succ k ih => exact fun _ _ h => ih _ _ h

/-- If the M-th power of the reflection class and the k-th power of U vanish on the Borel
cohomology of the iterated complex, the (M+1)k-th power of the class of the second involution
vanishes. -/
theorem v_nilpotent {M k : ℕ}
    (hW : ∀ (lo : ℕ) (x : HR (borelInv S) lo), innerPow S lo M x = 0)
    (hU : ∀ (q : ℕ) (x : HR (borelInv S) q), Ann S k q x) (lo : ℕ) (x : HR (borelInv S) lo) :
    Finsler.Gysin.word (V := fun i => HR (borelInv S) (lo + i))
      (fun i => (w (borelInv S) (lo + i)).toAddMonoidHom) ((M + 1) * k) x = 0 := by
  have hW2 : ∀ (lo : ℕ) (x : HR (borelInv S) lo),
      Finsler.Gysin.word (V := fun i => HR (borelInv S) (lo + i))
        (fun i => (innerStep S (lo + i)).toAddMonoidHom) M x = 0 := hW
  exact word_nilpotent (G := fun q => HR (borelInv S) q) (f := fun q => w (borelInv S) q)
    (g := fun q => innerStep S q) (fun q x => w_innerStep S q x) hW2
    (fun q x => annG_of_ann S k q x (hU q x)) lo x

end Classes

end

end Finsler.OperatorK
