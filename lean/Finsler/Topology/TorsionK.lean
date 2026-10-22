module

public import Finsler.Topology.VisibleBound

/-! Classes annihilated by a power of U = v(v + w) and the kernel of v at a finite cut. In a ring,
if V and W commute and W^M = 0, then V^{(M+1)k} = P·(V(V + W))^k for some P. Hence, for two
commuting families f, g of degree-one maps of a graded module with vanishing M-fold composites of
g, a single class annihilated by the k-th power of f(f + g) is annihilated by the (M+1)k-fold
composite of f. On the K-Borel cohomology of (t_{2a}, M) at a regular cut the reflection class is
nilpotent and v is injective in high degrees; so a class annihilated by a power of U is a
v-torsion class, and vanishes in high degrees. The classes annihilated by the k-th power of U
form a graded subspace stable under v, and this is natural. Therefore the restrictions to
(t_{2a}, M) of the global K-classes annihilated by the k-th power of U form a family of subspaces
stable under v which vanishes in high degrees, and the count for such families gives: the total
dimension of their forgetful images in the reflection Borel cohomology of (t_{2a}, M) is at most
the total dimension of the kernel of v. -/

@[expose] public section

namespace Finsler.TorsionK

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelLoop Finsler.BorelCochain
open Finsler.CriticalLevels Finsler.BorelIterate Finsler.BorelK Finsler.BorelFreeK
open Finsler.BorelCoverK Finsler.NilpotentWK Finsler.FiniteCut Finsler.OperatorK
open Finsler.VisibleBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### A ring identity -/

/-- In a ring, if V and W commute and W^M = 0, then V^{(M+1)k} is a left multiple of
(V(V + W))^k. -/
theorem exists_pow_eq_mul {R : Type*} [Ring R] {V W : R} (hc : Commute V W) {M : ℕ}
    (hW : W ^ M = 0) (k : ℕ) : ∃ P : R, V ^ ((M + 1) * k) = P * (V * (V + W)) ^ k := by
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
  refine ⟨(∑ i ∈ Finset.range M, V ^ i * (-W) ^ (M - 1 - i)) ^ k, ?_⟩
  rw [pow_mul, h1, hUQ.mul_pow]
  exact (hUQ.pow_pow k k).eq

/-! ### Single classes of a graded module -/

section Shift

variable {G : ℕ → Type} [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
  (f g : ∀ q, G q →ₗ[ZMod 2] G (q + 1))

/-- If every component of y is annihilated by the k-th power of f(f + g), the k-th power of the
endomorphism f(f + g) of the product annihilates y. -/
theorem shiftOp_U_pow_apply (k : ℕ) : ∀ (y : (q : ℕ) → G q), (∀ q, AnnG f g k q (y q)) →
    ((shiftOp G f * (shiftOp G f + shiftOp G g)) ^ k) y = 0 := by
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

/-- If f and g commute and the M-fold composites of g vanish, a class annihilated by the k-th
power of f(f + g) is annihilated by the (M+1)k-fold composite of f. -/
theorem word_eq_zero_of_annG (hcomm : ∀ q x, f (q + 1) (g q x) = g (q + 1) (f q x)) {M k : ℕ}
    (hg : ∀ (lo : ℕ) (x : G lo), Finsler.Gysin.word (V := fun i => G (lo + i))
      (fun i => (g (lo + i)).toAddMonoidHom) M x = 0)
    (lo : ℕ) (x : G lo) (hx : AnnG f g k lo x) :
    Finsler.Gysin.word (V := fun i => G (lo + i)) (fun i => (f (lo + i)).toAddMonoidHom)
      ((M + 1) * k) x = 0 := by
  obtain ⟨P, hP⟩ := exists_pow_eq_mul (shiftOp_commute f g hcomm) (shiftOp_pow_eq_zero g M hg) k
  have hy : ∀ q, AnnG f g k q ((Pi.single lo x : (q : ℕ) → G q) q) := by
    intro q
    by_cases hq : q = lo
    · subst hq
      rw [Pi.single_eq_same]
      exact hx
    · rw [Pi.single_eq_of_ne hq]
      exact annG_zero f g k q
  have h0 : (shiftOp G f ^ ((M + 1) * k)) (Pi.single lo x) = 0 := by
    rw [hP]
    change P (((shiftOp G f * (shiftOp G f + shiftOp G g)) ^ k) (Pi.single lo x)) = 0
    rw [shiftOp_U_pow_apply f g k (Pi.single lo x) hy, map_zero]
  have h1 := shiftOp_pow_apply f ((M + 1) * k) lo (Pi.single lo x)
  rw [h0, Pi.single_eq_same] at h1
  exact h1.symm

end Shift

/-! ### Classes annihilated by a power of U -/

section Classes

variable {K L : InvComplex} (S : Commuting K)

/-- The classes annihilated by the k-th power of U are stable under v. -/
theorem ann_w (k : ℕ) : ∀ (q : ℕ) (x : HR (borelInv S) q), Ann S k q x →
    Ann S k (q + 1) (w (borelInv S) q x) := by
  induction k with
  | zero =>
    intro q x hx
    change w (borelInv S) q x = 0
    rw [show x = 0 from hx, map_zero]
  | succ k ih =>
    intro q x hx
    change Ann S k (q + 1 + 1 + 1) (opU S (q + 1) (w (borelInv S) q x))
    have e : opU S (q + 1) (w (borelInv S) q x) = w (borelInv S) (q + 1 + 1) (opU S q x) := by
      rw [opU_apply, opU_apply]
      exact congrArg (w (borelInv S) (q + 1 + 1)) (by rw [map_add, w_innerStep])
    rw [e]
    exact ih _ _ hx

theorem ann_add (k : ℕ) : ∀ (q : ℕ) (x y : HR (borelInv S) q), Ann S k q x → Ann S k q y →
    Ann S k q (x + y) := by
  induction k with
  | zero =>
    intro q x y hx hy
    change x + y = 0
    rw [show x = 0 from hx, show y = 0 from hy, add_zero]
  | succ k ih =>
    intro q x y hx hy
    change Ann S k (q + 1 + 1) (opU S q (x + y))
    rw [map_add]
    exact ih _ _ _ hx hy

theorem ann_smul (k : ℕ) : ∀ (q : ℕ) (c : ZMod 2) (x : HR (borelInv S) q), Ann S k q x →
    Ann S k q (c • x) := by
  induction k with
  | zero =>
    intro q c x hx
    change c • x = 0
    rw [show x = 0 from hx, smul_zero]
  | succ k ih =>
    intro q c x hx
    change Ann S k (q + 1 + 1) (opU S q (c • x))
    rw [map_smul]
    exact ih _ _ _ hx

/-- The classes of degree q annihilated by the k-th power of U. -/
def annSub (k q : ℕ) : Submodule (ZMod 2) (HR (borelInv S) q) where
  carrier := {x | Ann S k q x}
  add_mem' := fun {x y} hx hy => ann_add S k q x y hx hy
  zero_mem' := ann_zero S k q
  smul_mem' := fun c {x} hx => ann_smul S k q c x hx

theorem mem_annSub (k q : ℕ) (x : HR (borelInv S) q) : x ∈ annSub S k q ↔ Ann S k q x :=
  Iff.rfl

/-- If the M-th power of the reflection class vanishes on the Borel cohomology of the iterated
complex, a class annihilated by the k-th power of U is annihilated by the (M+1)k-th power of the
class of the second involution. -/
theorem word_eq_zero_of_ann {M k : ℕ}
    (hW : ∀ (lo : ℕ) (x : HR (borelInv S) lo), innerPow S lo M x = 0) (lo : ℕ)
    (x : HR (borelInv S) lo) (hx : Ann S k lo x) :
    Finsler.Gysin.word (V := fun i => HR (borelInv S) (lo + i))
      (fun i => (w (borelInv S) (lo + i)).toAddMonoidHom) ((M + 1) * k) x = 0 := by
  have hW2 : ∀ (lo : ℕ) (x : HR (borelInv S) lo),
      Finsler.Gysin.word (V := fun i => HR (borelInv S) (lo + i))
        (fun i => (innerStep S (lo + i)).toAddMonoidHom) M x = 0 := hW
  exact word_eq_zero_of_annG (G := fun q => HR (borelInv S) q) (f := fun q => w (borelInv S) q)
    (g := fun q => innerStep S q) (fun q x => w_innerStep S q x) hW2 lo x
    (annG_of_ann S k lo x hx)

/-- If the ordinary cohomology of the iterated complex vanishes from degree Q on and a power of
the reflection class vanishes, a class of degree at least Q annihilated by a power of U is
zero. -/
theorem eq_zero_of_ann {Q M k : ℕ} (hzero : ∀ q, Q ≤ q → ∀ z : H (borelInv S) q, z = 0)
    (hW : ∀ (lo : ℕ) (x : HR (borelInv S) lo), innerPow S lo M x = 0) (q : ℕ) (hq : Q ≤ q)
    (x : HR (borelInv S) q) (hx : Ann S k q x) : x = 0 := by
  have hinj : ∀ i, Function.Injective (w (borelInv S) (q + i)).toAddMonoidHom := fun i => by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (exact_w (borelInv S) (q + i) y).mp hy
    rw [hzero (q + i) (by omega) z, map_zero]
  exact Finsler.TripleK.word_injective (V := fun i => HR (borelInv S) (q + i))
    (fun i => (w (borelInv S) (q + i)).toAddMonoidHom) hinj ((M + 1) * k)
    ((word_eq_zero_of_ann S hW q x hx).trans
      (word_eq_zero_of_ann S hW q 0 (ann_zero S k q)).symm)

end Classes

/-! ### The count at a regular cut -/

variable {n : ℕ} (F : ReversibleMetric n)

/-- With finitely many prime closed geodesic images, at a regular cut 2a and for D large: for
every k, the forgetful images of the restrictions to (t_{2a}, M) of the global K-classes
annihilated by the k-th power of U = v(v + w) have total dimension at most the total dimension
of the kernel of v on the K-Borel cohomology of (t_{2a}, M). -/
theorem exists_torsion_count (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q : ℕ, ∀ D, Q ≤ D → ∀ k : ℕ,
      ∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
          (((annSub (halfCommutingFull n) k q).map
            (HRmap (borelHom (resComm F (2 * a))) q)).map (forget (kComplex F (2 * a)) q)) ≤
        ∑ q ∈ Finset.range D,
          finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) := by
  have h2 : 0 < 2 * a := by linarith
  obtain ⟨Q, -, hzeroR⟩ := exists_finite_HR F hn hfin h2 h2a
  obtain ⟨M, hW⟩ := exists_innerW_nilpotent F hn hfin (2 * a) h2 h2a
  have hzero : ∀ q, Q ≤ q → ∀ z : H (kComplex F (2 * a)) q, z = 0 := fun q hq z => by
    apply (forgetTargetEquiv F (2 * a) q).injective
    exact (hzeroR q hq _).trans (hzeroR q hq _).symm
  refine ⟨Q, fun D hD k => ?_⟩
  refine torsion_bound F hn hfin ha h2a D
    (fun q => (annSub (halfCommutingFull n) k q).map (HRmap (borelHom (resComm F (2 * a))) q))
    ?_ ?_
  · rintro q _ ⟨y, hy, rfl⟩
    exact ⟨w (kFull n) q y, ann_w (halfCommutingFull n) k q y hy,
      HRmap_w (borelHom (resComm F (2 * a))) q y⟩
  · rw [Submodule.eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact eq_zero_of_ann (halfCommuting F (2 * a)) hzero hW D hD _
      (ann_map (resComm F (2 * a)) k D y hy)

end

end Finsler.TorsionK
