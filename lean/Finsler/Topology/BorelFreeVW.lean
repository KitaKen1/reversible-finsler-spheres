module

public import Finsler.Topology.BorelFreeV
public import Finsler.Topology.BorelInvolutionHomotopy

/-! The two classes on iterated Borel cohomology agree where both involutions exchange the two
pieces. The parity primitive of an involutive complex is a contraction of the componentwise
transfer on all Borel cochains: D(P_q c) + P_{q+1}(D c) = (1 + t) c. Hence, for an involutive
complex K with a second commuting involution s, the first involution acts as the identity on the
Borel cohomology of the iterated complex, as the second one does. A mixed multiplier is a family
of linear maps m commuting with the differential with t m + m t = t and s m + m s = s. For
Q = m ∘ s one has [d, Q] = 0, [1 + t, Q] = t s and [1 + s, Q] = 1, so applying Q componentwise to
a Borel cocycle C of the iterated complex gives a cochain whose total differential is C plus the
image of t s C under the inclusion of filtrations. Therefore the class v of the second
involution and the reflection class w agree on the Borel cohomology of the iterated complex.
For the relative cochains of a pair with two commuting involutions r and τ, a 0-cocycle π with
π + r^*π = 1 and π + τ^*π = 1 gives a mixed multiplier; this applies to the indicator of a
closed and open set exchanged with its complement by both involutions. -/

@[expose] public section

namespace Finsler.BorelFreeVW

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelIterate Finsler.BorelFree Finsler.BorelFreeK Finsler.BorelFreeV
open Finsler.BorelInvolutionHomotopy

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem eq_of_add_eq_zero {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M}
    (h : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [two_eq_zero_of_mod, add_zero]
    _ = x + y + y := by abel
    _ = y := by rw [h, zero_add]

theorem add_cancel_mid {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {a b t u c : M}
    (h1 : a + b = t) (h2 : u + b = c) : a + u = c + t := by
  rw [← h1, ← h2]
  calc a + u = a + u + (b + b) := by rw [two_eq_zero_of_mod, add_zero]
    _ = u + b + (a + b) := by abel

/-! ### The parity homotopy -/

section Parity

variable (K : InvComplex)

theorem parity_succ_succ (q j : ℕ) : parity (q + 1) (j + 1) = parity q j := by
  unfold parity
  push_cast
  ring

theorem parity_zero_add (q : ℕ) : parity q 0 + parity (q + 1) 0 = 1 := by
  have h2 : (q : ZMod 2) + (q : ZMod 2) = 0 := two_eq_zero_of_mod _
  unfold parity
  push_cast
  calc (q : ZMod 2) - 0 + ((q : ZMod 2) + 1 - 0) = (q : ZMod 2) + (q : ZMod 2) + 1 := by ring
    _ = 1 := by rw [h2, zero_add]

/-- The parity primitive is a contraction of the componentwise transfer on all Borel
cochains. -/
theorem primitive_homotopy (q : ℕ) (c : Seq K) :
    D K (primitive K q c) + primitive K (q + 1) (D K c) = fun j => tr K j (c j) := by
  funext j
  cases j with
  | zero =>
    change tr K 0 (parity q 0 • c 0) + parity (q + 1) 0 • tr K 0 (c 0) = tr K 0 (c 0)
    rw [map_smul, ← add_smul, parity_zero_add, one_smul]
  | succ j =>
    change K.d j (parity q j • c j) + tr K (j + 1) (parity q (j + 1) • c (j + 1)) +
      parity (q + 1) (j + 1) • (K.d j (c j) + tr K (j + 1) (c (j + 1))) =
        tr K (j + 1) (c (j + 1))
    rw [map_smul, map_smul, parity_succ_succ, smul_add]
    have h := parity_adjacent q j
    calc parity q j • K.d j (c j) + parity q (j + 1) • tr K (j + 1) (c (j + 1)) +
          (parity q j • K.d j (c j) + parity q j • tr K (j + 1) (c (j + 1)))
        = (parity q j • K.d j (c j) + parity q j • K.d j (c j)) +
          (parity q j + parity q (j + 1)) • tr K (j + 1) (c (j + 1)) := by
          rw [add_smul]
          abel
      _ = tr K (j + 1) (c (j + 1)) := by rw [two_eq_zero_of_mod, zero_add, h, one_smul]

theorem primitive_add (q : ℕ) (c c' : Seq K) :
    primitive K q (c + c') = primitive K q c + primitive K q c' := by
  funext j
  exact smul_add _ _ _

theorem primitive_zero_low {c : Seq K} (hc : c ∈ low K 1) : primitive K 0 c = 0 :=
  mem_low_zero K (primitive_low K 0 c hc)

end Parity

/-! ### The first involution on the iterated complex -/

section Rho

variable {K : InvComplex} (S : Commuting K)

theorem seqOf_zero (n : ℕ) : seqOf S n 0 = 0 := rfl

theorem primitive_seqS (q : ℕ) (c : Seq K) :
    primitive K q (seqS S c) = seqS S (primitive K q c) := by
  funext j
  change parity q j • S.s j (c j) = S.s j (parity q j • c j)
  rw [map_smul]

/-- The first involution as a map commuting with the second involution. -/
def rhoComm : CommHom S S where
  φ := involutionHom K
  comm_s j x := (S.st j x).symm

/-- The parity primitive on the cochains of the iterated complex. -/
def prim (j : ℕ) (x : (borelInv S).C (j + 1)) : (borelInv S).C j :=
  ofLow S j ⟨primitive K (j + 1) (seqOf S (j + 1) x),
    primitive_low K (j + 1) _ (toLow S (j + 1) x).2⟩

theorem seqOf_prim (j : ℕ) (x : (borelInv S).C (j + 1)) :
    seqOf S j (prim S j x) = primitive K (j + 1) (seqOf S (j + 1) x) := rfl

/-- The cocycle condition of the iterated complex in terms of the underlying Borel cochains. -/
theorem cocycle_tr (c : Seq (borelInv S)) (hc : D (borelInv S) c = 0) (j : ℕ) :
    seqOf S (j + 1) (c (j + 1)) + seqS S (seqOf S (j + 1) (c (j + 1))) =
      D K (seqOf S j (c j)) := by
  have h1 : seqOf S (j + 1) (D (borelInv S) c (j + 1)) = 0 := by
    rw [hc]
    rfl
  have h2 : D K (seqOf S j (c j)) +
      (seqOf S (j + 1) (c (j + 1)) + seqS S (seqOf S (j + 1) (c (j + 1)))) = 0 := h1
  exact (eq_of_add_eq_zero h2).symm

/-- The total differential of the parity primitive of a cocycle of the iterated complex. -/
theorem seqOf_D_prim (c : Seq (borelInv S)) (hc : D (borelInv S) c = 0) (j : ℕ) :
    seqOf S j (D (borelInv S) (fun i => prim S i (c (i + 1))) j) =
      fun i => tr K i (seqOf S j (c j) i) := by
  cases j with
  | zero =>
    change primitive K (0 + 1) (seqOf S (0 + 1) (c (0 + 1))) +
      seqS S (primitive K (0 + 1) (seqOf S (0 + 1) (c (0 + 1)))) = _
    rw [← primitive_seqS, ← primitive_add, cocycle_tr S c hc 0]
    have h := primitive_homotopy K 0 (seqOf S 0 (c 0))
    have hP0 : primitive K 0 (seqOf S 0 (c 0)) = 0 :=
      primitive_zero_low K (toLow S 0 (c 0)).2
    rw [hP0, map_zero, zero_add] at h
    exact h
  | succ j =>
    change D K (primitive K (j + 1) (seqOf S (j + 1) (c (j + 1)))) +
      (primitive K (j + 1 + 1) (seqOf S (j + 1 + 1) (c (j + 1 + 1))) +
        seqS S (primitive K (j + 1 + 1) (seqOf S (j + 1 + 1) (c (j + 1 + 1))))) = _
    rw [← primitive_seqS, ← primitive_add, cocycle_tr S c hc (j + 1)]
    exact primitive_homotopy K (j + 1) (seqOf S (j + 1) (c (j + 1)))

/-- The first involution acts as the identity on the Borel cohomology of the iterated
complex. -/
theorem rho_HR (n : ℕ) (x : HR (borelInv S) n) : HRmap (borelHom (rhoComm S)) n x = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc := (mem_bcocycles (borelInv S)).mp c.2
  change Submodule.Quotient.mk (bcocycleMap (borelHom (rhoComm S)) n c) =
    Submodule.Quotient.mk c
  apply eq_of_add_eq_zero
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
  change seqMap (borelHom (rhoComm S)) c.val + c.val ∈ bcoboundaries (borelInv S) n
  refine ⟨fun j => prim S j (c.val (j + 1)), ?_, ?_⟩
  · intro j hj
    have h0 : c.val (j + 1) = 0 := hc.1 (j + 1) (by omega)
    change prim S j (c.val (j + 1)) = 0
    rw [h0]
    apply seqOf_injective S
    rw [seqOf_prim]
    funext i
    exact smul_zero _
  · funext j
    apply seqOf_injective S
    rw [seqOf_D_prim S c.val hc.2 j]
    funext i
    change tr K i (seqOf S j (c.val j) i) =
      K.t i (seqOf S j (c.val j) i) + seqOf S j (c.val j) i
    rw [tr_apply, add_comm]

end Rho

/-! ### Mixed multipliers -/

section Mixed

variable {K : InvComplex}

/-- A multiplier commuting with the differential which both involutions change by the
identity: t m + m t = t and s m + m s = s. -/
structure Mixed (S : Commuting K) where
  m : (j : ℕ) → K.C j →ₗ[ZMod 2] K.C j
  comm_d : ∀ j x, K.d j (m j x) = m (j + 1) (K.d j x)
  swap_t : ∀ j x, K.t j (m j x) + m j (K.t j x) = K.t j x
  swap_s : ∀ j x, S.s j (m j x) + m j (S.s j x) = S.s j x

variable {S : Commuting K} (h : Mixed S)

/-- The multiplier after the second involution. -/
def qm (j : ℕ) : K.C j →ₗ[ZMod 2] K.C j := h.m j ∘ₗ S.s j

theorem qm_apply (j : ℕ) (x : K.C j) : qm h j x = h.m j (S.s j x) := rfl

theorem qm_d (j : ℕ) (x : K.C j) : K.d j (qm h j x) = qm h (j + 1) (K.d j x) := by
  rw [qm_apply, qm_apply, h.comm_d, S.sd]

theorem qm_tr (j : ℕ) (x : K.C j) :
    tr K j (qm h j x) + qm h j (tr K j x) = K.t j (S.s j x) := by
  have e := h.swap_t j (S.s j x)
  rw [qm_apply, qm_apply, tr_apply, tr_apply, map_add, map_add, S.st]
  calc h.m j (S.s j x) + K.t j (h.m j (S.s j x)) +
        (h.m j (S.s j x) + h.m j (K.t j (S.s j x)))
      = (h.m j (S.s j x) + h.m j (S.s j x)) +
        (K.t j (h.m j (S.s j x)) + h.m j (K.t j (S.s j x))) := by abel
    _ = K.t j (S.s j x) := by rw [two_eq_zero_of_mod, zero_add, e]

theorem qm_s (j : ℕ) (x : K.C j) :
    qm h j x + S.s j (qm h j x) + qm h j (x + S.s j x) = x := by
  have e := h.swap_s j (S.s j x)
  rw [S.ss] at e
  rw [qm_apply, qm_apply, map_add, map_add, S.ss]
  calc h.m j (S.s j x) + S.s j (h.m j (S.s j x)) + (h.m j (S.s j x) + h.m j x)
      = (h.m j (S.s j x) + h.m j (S.s j x)) + (S.s j (h.m j (S.s j x)) + h.m j x) := by abel
    _ = x := by rw [two_eq_zero_of_mod, zero_add, e]

/-- The multiplier after the second involution, applied componentwise. -/
def mSeq : Seq K →ₗ[ZMod 2] Seq K := LinearMap.pi fun j => qm h j ∘ₗ LinearMap.proj j

theorem mSeq_apply (c : Seq K) (j : ℕ) : mSeq h c j = qm h j (c j) := rfl

theorem mSeq_low {k : ℕ} {c : Seq K} (hc : c ∈ low K k) : mSeq h c ∈ low K k := by
  intro j hj
  rw [mSeq_apply, hc j hj, map_zero]

theorem mSeq_s (c : Seq K) : mSeq h c + seqS S (mSeq h c) + mSeq h (c + seqS S c) = c := by
  funext j
  exact qm_s h j (c j)

/-- The commutator with the Borel differential is the componentwise composite of the two
involutions. -/
theorem D_mSeq (c : Seq K) :
    D K (mSeq h c) + mSeq h (D K c) = fun j => K.t j (S.s j (c j)) := by
  funext j
  cases j with
  | zero =>
    change tr K 0 (qm h 0 (c 0)) + qm h 0 (tr K 0 (c 0)) = K.t 0 (S.s 0 (c 0))
    exact qm_tr h 0 (c 0)
  | succ j =>
    change K.d j (qm h j (c j)) + tr K (j + 1) (qm h (j + 1) (c (j + 1))) +
      qm h (j + 1) (K.d j (c j) + tr K (j + 1) (c (j + 1))) =
        K.t (j + 1) (S.s (j + 1) (c (j + 1)))
    rw [map_add, qm_d]
    calc qm h (j + 1) (K.d j (c j)) + tr K (j + 1) (qm h (j + 1) (c (j + 1))) +
          (qm h (j + 1) (K.d j (c j)) + qm h (j + 1) (tr K (j + 1) (c (j + 1))))
        = (qm h (j + 1) (K.d j (c j)) + qm h (j + 1) (K.d j (c j))) +
          (tr K (j + 1) (qm h (j + 1) (c (j + 1))) +
            qm h (j + 1) (tr K (j + 1) (c (j + 1)))) := by abel
      _ = K.t (j + 1) (S.s (j + 1) (c (j + 1))) := by
          rw [two_eq_zero_of_mod, zero_add, qm_tr]

/-- The componentwise homotopy on the cochains of the iterated complex. -/
def qL (j : ℕ) : (borelInv S).C j →ₗ[ZMod 2] (borelInv S).C j :=
  (mSeq h).restrict (fun _ hc => mSeq_low h hc)

theorem seqOf_qL (j : ℕ) (x : (borelInv S).C j) :
    seqOf S j (qL h j x) = mSeq h (seqOf S j x) := rfl

/-- The reflection shift of the iterated complex in terms of the underlying Borel cochains. -/
theorem seqOf_total (Z : Seq (borelInv S)) (j : ℕ) :
    seqOf S (j + 1) (BorelGraded.total (innerW S) Z (j + 1)) = seqOf S j (Z j) := by
  have key : ∀ (k : ℕ) (_ : k = 1 + j),
      seqOf S k (BorelGraded.total (innerW S) Z k) = seqOf S j (Z j) := by
    intro k hk
    subst hk
    rw [BorelGraded.total_at]
    rfl
  exact key (j + 1) (Nat.add_comm j 1)

/-- The total differential of the homotopy applied to a cocycle C of the iterated complex is C
plus the reflection shift of t s C. -/
theorem D_qL (c : Seq (borelInv S)) (hc : D (borelInv S) c = 0) :
    D (borelInv S) (fun j => qL h j (c j)) =
      c + BorelGraded.total (innerW S)
        (seqMap (borelHom (rhoComm S)) (seqMap (involutionHom (borelInv S)) c)) := by
  funext j
  apply seqOf_injective S
  cases j with
  | zero =>
    change mSeq h (seqOf S 0 (c 0)) + seqS S (mSeq h (seqOf S 0 (c 0))) =
      seqOf S 0 (c 0) + seqOf S 0 (BorelGraded.total (innerW S)
        (seqMap (borelHom (rhoComm S)) (seqMap (involutionHom (borelInv S)) c)) 0)
    rw [BorelGraded.total_below (innerW S) _ (show 0 < 1 by omega), seqOf_zero, add_zero]
    have h0 : seqOf S 0 (c 0) + seqS S (seqOf S 0 (c 0)) = 0 :=
      congrArg (seqOf S 0) (congrFun hc 0)
    have e := mSeq_s h (seqOf S 0 (c 0))
    rw [h0, map_zero, add_zero] at e
    exact e
  | succ j =>
    change D K (mSeq h (seqOf S j (c j))) +
        (mSeq h (seqOf S (j + 1) (c (j + 1))) +
          seqS S (mSeq h (seqOf S (j + 1) (c (j + 1))))) =
      seqOf S (j + 1) (c (j + 1)) + seqOf S (j + 1) (BorelGraded.total (innerW S)
        (seqMap (borelHom (rhoComm S)) (seqMap (involutionHom (borelInv S)) c)) (j + 1))
    rw [seqOf_total]
    have e1 := D_mSeq h (seqOf S j (c j))
    have e2 := mSeq_s h (seqOf S (j + 1) (c (j + 1)))
    rw [cocycle_tr S c hc j] at e2
    exact add_cancel_mid e1 e2

include h in
/-- With a mixed multiplier, the class of the second involution and the reflection class agree
on the Borel cohomology of the iterated complex. -/
theorem outerW_eq_innerW (n : ℕ) (x : HR (borelInv S) n) :
    w (borelInv S) n x = innerStep S n x := by
  have hx : HRmap (borelHom (rhoComm S)) n (HRmap (involutionHom (borelInv S)) n x) = x := by
    rw [rho_HR, involution_HR]
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [innerStep_apply]
  have hc := (mem_bcocycles (borelInv S)).mp c.2
  have hmem : BorelGraded.total (innerW S)
      (seqMap (borelHom (rhoComm S)) (seqMap (involutionHom (borelInv S)) c.val)) ∈
      bcocycles (borelInv S) (n + 1) := by
    rw [Nat.add_comm n 1]
    exact (BorelGraded.cyclesMap (innerW S) n (bcocycleMap (borelHom (rhoComm S)) n
      (bcocycleMap (involutionHom (borelInv S)) n c))).2
  have h2 : BorelGraded.castHR (Nat.add_comm 1 n) (BorelGraded.onHR (innerW S) n
      (HRmap (borelHom (rhoComm S)) n (HRmap (involutionHom (borelInv S)) n
        (Submodule.Quotient.mk c)))) =
      Submodule.Quotient.mk (⟨BorelGraded.total (innerW S)
        (seqMap (borelHom (rhoComm S)) (seqMap (involutionHom (borelInv S)) c.val)), hmem⟩ :
        bcocycles (borelInv S) (n + 1)) :=
    BorelGraded.castHR_mk _ _ _ _
  rw [hx] at h2
  rw [h2]
  apply eq_of_add_eq_zero
  change (Submodule.Quotient.mk (Submodule.inclusion (bcocycles_mono (borelInv S) n) c) :
    HR (borelInv S) (n + 1)) + _ = 0
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
  change c.val + BorelGraded.total (innerW S)
      (seqMap (borelHom (rhoComm S)) (seqMap (involutionHom (borelInv S)) c.val)) ∈
    bcoboundaries (borelInv S) (n + 1)
  refine ⟨fun j => qL h j (c.val j), ?_, D_qL h c.val hc.2⟩
  intro j hj
  change qL h j (c.val j) = 0
  rw [hc.1 j hj, map_zero]

end Mixed

/-! ### Pairs with two involutions -/

section Pair

variable (P : TopPair.{0})

theorem swap_aux (f : P ⟶ P) (π : singularCochainGroup (ZMod 2) P.fst 0)
    (hπ : π + cochainPullback (TopPair.Hom.fst f) 0 π = cochainOne (R := ZMod 2) (Z := P.fst))
    (j : ℕ) (x : RelativeCupCochain.relative P j) :
    RelativeCupCochain.pullback f j (mul P π j x) +
      mul P π j (RelativeCupCochain.pullback f j x) = RelativeCupCochain.pullback f j x := by
  rw [pullback_mul, ← mul_add_left, add_comm (cochainPullback (TopPair.Hom.fst f) 0 π) π, hπ,
    mul_one]

/-- The indicator cocycle of a set exchanged with its complement by a map of pairs. -/
theorem indicator_add_pullback (f : P ⟶ P) (U : Set P.fst)
    (hswap : ∀ x : P.fst, (TopPair.Hom.fst f).hom x ∈ U ↔ x ∉ U) :
    pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2))) +
      cochainPullback (TopPair.Hom.fst f) 0
        (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) =
      cochainOne (R := ZMod 2) (Z := P.fst) := by
  rw [pointCochain_pullback]
  apply cochain_ext
  intro σ
  rw [cochainEval_add, pointCochain_eval, pointCochain_eval, cochainOne_eval]
  by_cases hx : simplexPoint P.fst σ ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (fun h => ((hswap _).mp h) hx),
      add_zero]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem ((hswap _).mpr hx), zero_add]

variable (r τ : P ⟶ P) (hr : r ≫ r = 𝟙 P) (hτ : τ ≫ τ = 𝟙 P) (hc : τ ≫ r = r ≫ τ)
  (π : singularCochainGroup (ZMod 2) P.fst 0)

/-- The mixed multiplier of the relative cochains of a pair with two commuting involutions r and
τ from a 0-cocycle π with π + r^*π = 1 and π + τ^*π = 1. -/
def mixed (hδ : cochainCoboundary (ZMod 2) P.fst 0 π = 0)
    (hπr : π + cochainPullback (TopPair.Hom.fst r) 0 π = cochainOne (R := ZMod 2) (Z := P.fst))
    (hπτ : π + cochainPullback (TopPair.Hom.fst τ) 0 π = cochainOne (R := ZMod 2) (Z := P.fst)) :
    Mixed (BorelInvariance.commuting hr τ hτ hc) where
  m j := mul P π j
  comm_d j x := differential_mul P π hδ j x
  swap_t j x := swap_aux P r π hπr j x
  swap_s j x := swap_aux P τ π hπτ j x

/-- If both involutions of a pair exchange a closed and open subset U of the space with its
complement, the class of the second involution and the reflection class agree on the iterated
Borel cohomology of the pair. -/
theorem outerW_eq_innerW_of_isClopen (U : Set P.fst) (hU : IsClopen U)
    (hswapτ : ∀ x : P.fst, (TopPair.Hom.fst τ).hom x ∈ U ↔ x ∉ U)
    (hswapr : ∀ x : P.fst, (TopPair.Hom.fst r).hom x ∈ U ↔ x ∉ U) (q : ℕ)
    (x : HR (borelInv (BorelInvariance.commuting hr τ hτ hc)) q) :
    w (borelInv (BorelInvariance.commuting hr τ hτ hc)) q x =
      innerStep (BorelInvariance.commuting hr τ hτ hc) q x := by
  have hδ : cochainCoboundary (ZMod 2) P.fst 0
      (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) = 0 :=
    pointCochain_coboundary P.fst _ (fun σ x y => indicator_eq_of_isClopen P.fst hU σ x y)
  exact outerW_eq_innerW (mixed P r τ hr hτ hc _ hδ (indicator_add_pullback P r U hswapr)
    (indicator_add_pullback P τ U hswapτ)) q x

end Pair

end

end Finsler.BorelFreeVW
