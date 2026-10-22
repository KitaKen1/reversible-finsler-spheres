module

public import Finsler.Algebra.PeriodicKernel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic

/-! The second-order linear recursion along a closed chain and its monodromy. The coefficients
are linear maps T_j (bijective), A_j, B_j of a space V, indexed by the residues modulo N; a
solution is a family w with T_j w_{j+1} + A_j w_j + B_j w_{j-1} = 0 for all j. The step map
sends (w_{j-1}, w_j) to (w_j, w_{j+1}), the propagator of k steps is the composite of the first
k step maps, and the monodromy M is the propagator of N steps. Solutions correspond to the
vectors fixed by M through w ↦ (w_0, w_1). For the m-fold iterated coefficients (period N
repeated m times, indexed modulo m N) the monodromy is M^m, so the dimension of the space of
solutions of the iterated recursion is the dimension of the space of the vectors fixed by M^m.
This is the linear algebra of the nullities of the iterates of a closed polygon (discrete
Jacobi fields and the linearized Poincaré map). -/

@[expose] public section

namespace Finsler.JacobiChain

open Module Finsler.PeriodicKernel

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The coefficients of a second-order recursion along a closed chain of N indices. -/
@[ext]
structure Coeff (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : ℕ) where
  /-- coefficient of the next member -/
  T : ZMod N → V ≃ₗ[ℝ] V
  /-- coefficient of the current member -/
  A : ZMod N → V →ₗ[ℝ] V
  /-- coefficient of the previous member -/
  B : ZMod N → V →ₗ[ℝ] V

variable {N : ℕ}

/-- The residual of the recursion at the index j. -/
def res (c : Coeff V N) (w : ZMod N → V) (j : ZMod N) : V :=
  c.T j (w (j + 1)) + c.A j (w j) + c.B j (w (j - 1))

/-- The step map: (w_{j-1}, w_j) ↦ (w_j, w_{j+1}). -/
def step (c : Coeff V N) (j : ZMod N) : V × V →ₗ[ℝ] V × V :=
  (LinearMap.snd ℝ V V).prod
    (-((c.T j).symm.toLinearMap ∘ₗ
      (c.A j ∘ₗ LinearMap.snd ℝ V V + c.B j ∘ₗ LinearMap.fst ℝ V V)))

theorem step_apply (c : Coeff V N) (j : ZMod N) (x : V × V) :
    step c j x = (x.2, -(c.T j).symm (c.A j x.2 + c.B j x.1)) := rfl

/-- The propagator of k steps, starting with the step at the index 1. -/
def prop (c : Coeff V N) : ℕ → (V × V →ₗ[ℝ] V × V)
  | 0 => LinearMap.id
  | k + 1 => step c ((k + 1 : ℕ) : ZMod N) ∘ₗ prop c k

theorem prop_zero (c : Coeff V N) (x : V × V) : prop c 0 x = x := rfl

theorem prop_succ (c : Coeff V N) (k : ℕ) (x : V × V) :
    prop c (k + 1) x = step c ((k + 1 : ℕ) : ZMod N) (prop c k x) := rfl

/-- The second component after k steps is the first component after k + 1 steps. -/
theorem prop_snd (c : Coeff V N) (k : ℕ) (x : V × V) : (prop c k x).2 = (prop c (k + 1) x).1 := by
  rw [prop_succ, step_apply]

/-- The monodromy: the propagator of one period. -/
def mono (c : Coeff V N) : V × V →ₗ[ℝ] V × V := prop c N

/-- The step maps reproduce a solution. -/
theorem prop_of_res (c : Coeff V N) {w : ZMod N → V} (hw : ∀ j, res c w j = 0) (k : ℕ) :
    prop c k (w 0, w 1) = (w (k : ZMod N), w ((k : ZMod N) + 1)) := by
  induction k with
  | zero =>
    rw [prop_zero, Nat.cast_zero, zero_add]
  | succ k ih =>
    rw [prop_succ, ih, step_apply]
    have h := hw ((k + 1 : ℕ) : ZMod N)
    rw [res, Nat.cast_succ, add_sub_cancel_right] at h
    have h2 : w ((k : ZMod N) + 1 + 1) =
        -(c.T ((k : ZMod N) + 1)).symm
          (c.A ((k : ZMod N) + 1) (w ((k : ZMod N) + 1)) + c.B ((k : ZMod N) + 1) (w k)) := by
      rw [← map_neg, LinearEquiv.eq_symm_apply]
      rw [add_assoc] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [Nat.cast_succ]
    exact Prod.ext rfl h2.symm

/-- A solution gives a vector fixed by the monodromy. -/
theorem mono_of_res (c : Coeff V N) {w : ZMod N → V} (hw : ∀ j, res c w j = 0) :
    mono c (w 0, w 1) = (w 0, w 1) := by
  rw [mono, prop_of_res c hw N, ZMod.natCast_self, zero_add]

/-- The propagator of k + N steps is the propagator of k steps after the monodromy. -/
theorem prop_add_period (c : Coeff V N) (k : ℕ) (x : V × V) :
    prop c (k + N) x = prop c k (mono c x) := by
  induction k with
  | zero => rw [zero_add, prop_zero, mono]
  | succ k ih =>
    have hidx : ((k + N + 1 : ℕ) : ZMod N) = ((k + 1 : ℕ) : ZMod N) := by
      push_cast
      rw [ZMod.natCast_self, add_zero]
    rw [Nat.add_right_comm, prop_succ, hidx, ih, prop_succ]

/-- Along a vector fixed by the monodromy the propagator is periodic. -/
theorem prop_add_mul (c : Coeff V N) {x : V × V} (hx : mono c x = x) (r t : ℕ) :
    prop c (r + N * t) x = prop c r x := by
  induction t with
  | zero => rw [Nat.mul_zero, add_zero]
  | succ t ih => rw [Nat.mul_succ, ← add_assoc, prop_add_period, hx, ih]

/-- The propagator of m periods is the m-th power of the monodromy. -/
theorem prop_mul_period (c : Coeff V N) (m : ℕ) : prop c (m * N) = mono c ^ m := by
  induction m with
  | zero =>
    rw [Nat.zero_mul, pow_zero]
    rfl
  | succ m ih =>
    refine LinearMap.ext fun x => ?_
    rw [Nat.succ_mul, prop_add_period, ih, pow_succ]
    rfl

/-- The family generated by a vector. -/
def gen (c : Coeff V N) (x : V × V) (j : ZMod N) : V := (prop c j.val x).1

theorem gen_zero (c : Coeff V N) (x : V × V) : gen c x 0 = x.1 := by
  rw [gen, ZMod.val_zero, prop_zero]

theorem prop_fst (c : Coeff V N) {x : V × V} (hx : mono c x = x) (k : ℕ) :
    (prop c k x).1 = gen c x (k : ZMod N) := by
  rw [gen, ZMod.val_natCast]
  have h := prop_add_mul c hx (k % N) (k / N)
  rw [Nat.mod_add_div] at h
  rw [h]

theorem gen_one (c : Coeff V N) {x : V × V} (hx : mono c x = x) : gen c x 1 = x.2 := by
  have h := prop_fst c hx 1
  rw [Nat.cast_one] at h
  rw [← h, ← prop_snd, prop_zero]

section Period

variable [NeZero N]

/-- The family generated by a vector fixed by the monodromy is a solution. -/
theorem res_gen (c : Coeff V N) {x : V × V} (hx : mono c x = x) (j : ZMod N) :
    res c (gen c x) j = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((k + 1 : ℕ) : ZMod N) = j :=
    ⟨(j - 1).val, by rw [Nat.cast_succ, ZMod.natCast_zmod_val, sub_add_cancel]⟩
  have h1 : (prop c k x).1 = gen c x (j - 1) := by
    rw [prop_fst c hx, ← hk, Nat.cast_succ, add_sub_cancel_right]
  have h2 : (prop c k x).2 = gen c x j := by
    rw [prop_snd, prop_fst c hx, hk]
  have h3 : (prop c (k + 1) x).2 = gen c x (j + 1) := by
    rw [prop_snd, prop_fst c hx, Nat.cast_succ, hk]
  have h4 : (prop c (k + 1) x).2 = -(c.T j).symm (c.A j (prop c k x).2 + c.B j (prop c k x).1) := by
    rw [prop_succ, step_apply, hk]
  rw [h3, h2, h1] at h4
  rw [res, h4, map_neg, LinearEquiv.apply_symm_apply, add_assoc]
  exact neg_add_cancel _

/-- A solution is generated by its members at the indices 0 and 1. -/
theorem gen_of_res (c : Coeff V N) {w : ZMod N → V} (hw : ∀ j, res c w j = 0) (j : ZMod N) :
    gen c (w 0, w 1) j = w j := by
  rw [gen, prop_of_res c hw, ZMod.natCast_zmod_val]

/-- **Solutions and the monodromy.** If the kernel of an operator on the closed chain is the
space of the solutions of the recursion, its dimension is the dimension of the space of the
vectors fixed by the monodromy. -/
theorem finrank_ker_eq (c : Coeff V N)
    (H : PiLp 2 (fun _ : ZMod N => V) →ₗ[ℝ] PiLp 2 (fun _ : ZMod N => V))
    (hH : ∀ w, H w = 0 ↔ ∀ j : ZMod N, res c (fun i => w i) j = 0) :
    finrank ℝ (LinearMap.ker H) = finrank ℝ (fixedPow (mono c) 1) := by
  set φ : LinearMap.ker H →ₗ[ℝ] V × V :=
    { toFun := fun w => ((w : PiLp 2 (fun _ : ZMod N => V)) 0, (w : PiLp 2 (fun _ : ZMod N => V)) 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hφ
  have hsol : ∀ w : LinearMap.ker H, ∀ j : ZMod N,
      res c (fun i => (w : PiLp 2 (fun _ : ZMod N => V)) i) j = 0 :=
    fun w => (hH w).mp (LinearMap.mem_ker.mp w.2)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h0 : (w : PiLp 2 (fun _ : ZMod N => V)) 0 = 0 := congrArg Prod.fst hw
    have h1 : (w : PiLp 2 (fun _ : ZMod N => V)) 1 = 0 := congrArg Prod.snd hw
    apply Subtype.ext
    refine PiLp.ext fun i => ?_
    have h : gen c ((w : PiLp 2 (fun _ : ZMod N => V)) 0, (w : PiLp 2 (fun _ : ZMod N => V)) 1) i =
        (w : PiLp 2 (fun _ : ZMod N => V)) i := gen_of_res c (hsol w) i
    rw [h0, h1] at h
    rw [← h, gen, Prod.mk_zero_zero, map_zero]
    rfl
  have hrange : LinearMap.range φ = fixedPow (mono c) 1 := by
    ext x
    rw [mem_fixedPow, pow_one, LinearMap.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact mono_of_res c (hsol w)
    · intro hx
      have hker : H (WithLp.toLp 2 (gen c x)) = 0 := (hH _).mpr (res_gen c hx)
      exact ⟨⟨WithLp.toLp 2 (gen c x), LinearMap.mem_ker.mpr hker⟩,
        Prod.ext (gen_zero c x) (gen_one c hx)⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]

end Period

section Iterate

variable (m : ℕ)

/-- The coefficients of the m-fold iterated chain. -/
def iter (c : Coeff V N) : Coeff V (m * N) where
  T j := c.T (ZMod.castHom (Dvd.intro_left m rfl) (ZMod N) j)
  A j := c.A (ZMod.castHom (Dvd.intro_left m rfl) (ZMod N) j)
  B j := c.B (ZMod.castHom (Dvd.intro_left m rfl) (ZMod N) j)

theorem step_iter (c : Coeff V N) (j : ZMod (m * N)) :
    step (iter m c) j = step c (ZMod.castHom (Dvd.intro_left m rfl) (ZMod N) j) := rfl

/-- The propagators of the iterated chain are those of the chain. -/
theorem prop_iter (c : Coeff V N) (k : ℕ) : prop (iter m c) k = prop c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    refine LinearMap.ext fun x => ?_
    rw [prop_succ, prop_succ, step_iter, ih, map_natCast]

/-- The monodromy of the m-fold iterated chain is the m-th power of the monodromy. -/
theorem mono_iter (c : Coeff V N) : mono (iter m c) = mono c ^ m := by
  rw [mono, prop_iter, prop_mul_period]

/-- **The nullities of the iterates.** If the kernel of an operator on the m-fold iterated
chain is the space of the solutions of the iterated recursion, its dimension is the dimension
of the space of the vectors fixed by the m-th power of the monodromy. -/
theorem finrank_ker_iter [NeZero m] [NeZero N] (c : Coeff V N)
    (H : PiLp 2 (fun _ : ZMod (m * N) => V) →ₗ[ℝ] PiLp 2 (fun _ : ZMod (m * N) => V))
    (hH : ∀ w, H w = 0 ↔ ∀ j : ZMod (m * N), res (iter m c) (fun i => w i) j = 0) :
    finrank ℝ (LinearMap.ker H) = finrank ℝ (fixedPow (mono c) m) := by
  rw [finrank_ker_eq (iter m c) H hH, mono_iter, fixedPow_pow, mul_one]

end Iterate

end

end Finsler.JacobiChain
