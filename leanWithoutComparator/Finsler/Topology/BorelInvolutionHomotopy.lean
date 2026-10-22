module
public import Finsler.Topology.BorelCochain
public import Mathlib.Tactic.Ring
/-! For every actual F₂ involutive cochain complex, adjacent group-degree parity coefficients sum to one. Multiplying a Borel cocycle component in vertical degree j by q-j in F₂ gives an explicit primitive supported below q for its componentwise transfer. The original involution therefore induces the identity on Borel cohomology, including degree zero. This is an explicit boundary proof, with no invariance assumption on individual cocycle components. -/

@[expose] public section
namespace Finsler.BorelInvolutionHomotopy
open Finsler.BorelCochain
noncomputable section
variable (K : InvComplex)

/-- Adjacent group-degree parity coefficients, expressed in F₂ to avoid truncated subtraction. -/
def parity (q j : ℕ) : ZMod 2 := (q : ZMod 2)- (j : ZMod 2)

theorem parity_adjacent (q j : ℕ) : parity q j+parity q (j+1)=1 := by
  unfold parity
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ = ((q : ZMod 2)+(q : ZMod 2))-((j : ZMod 2)+(j : ZMod 2))-1 := by ring
    _ = 1 := by rw [two_eq_zero_of_mod,two_eq_zero_of_mod];decide

/-- Explicit parity primitive for the transfer of a Borel cocycle. -/
def primitive (q : ℕ) (c : Seq K) : Seq K := fun j => parity q j • c j

theorem primitive_low (q : ℕ) (c : Seq K) (hc : c ∈ low K (q+1)) : primitive K q c ∈ low K q := by
  intro j hj
  change parity q j • c j=0
  by_cases he : j=q
  · subst j
    simp only [parity,sub_self,zero_smul]
  · rw [hc j (by omega),smul_zero]

theorem cocycle_d_eq_tr (c : Seq K) (hc : D K c=0) (j : ℕ) : K.d j (c j)=tr K (j+1) (c (j+1)) := by
  have h := congrFun hc (j+1)
  rw [D_succ] at h
  change K.d j (c j)+tr K (j+1) (c (j+1))=0 at h
  calc
    _ = K.d j (c j)+(tr K (j+1) (c (j+1))+tr K (j+1) (c (j+1))) := by rw [two_eq_zero_of_mod,add_zero]
    _ = _ := by rw [←add_assoc,h,zero_add]

theorem primitive_D (q : ℕ) (c : Seq K) (hc : D K c=0) :
    D K (primitive K q c) = fun j => tr K j (c j) := by
  funext j
  cases j with
  | zero =>
    have h : tr K 0 (c 0)=0 := congrFun hc 0
    change tr K 0 (parity q 0 • c 0)=tr K 0 (c 0)
    rw [map_smul,h,smul_zero]
  | succ j =>
    rw [D_succ]
    change K.d j (parity q j • c j)+tr K (j+1) (parity q (j+1) • c (j+1))=tr K (j+1) (c (j+1))
    rw [map_smul,map_smul,cocycle_d_eq_tr K c hc,←add_smul,parity_adjacent,one_smul]

theorem transfer_boundary (q : ℕ) (c : bcocycles K q) :
    (fun j => tr K j (c.val j)) ∈ bcoboundaries K q := by
  refine ⟨primitive K q c.val,primitive_low K q c.val ((mem_bcocycles K).mp c.2).1,?_⟩
  exact primitive_D K q c.val ((mem_bcocycles K).mp c.2).2

/-- The original involution is an actual map of its Borel total complex. -/
def involutionHom : InvHom K K where
  f := K.t
  comm_d j x := K.td j x
  comm_t _j _x := rfl

/-- The explicit parity primitive makes the original involution act identically on Borel cohomology. -/
theorem involution_HR (q : ℕ) (x : HR K q) : HRmap (involutionHom K) q x=x := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (bcocycleMap (involutionHom K) q c)=Submodule.Quotient.mk c
  apply sub_eq_zero.mp
  rw [←Submodule.Quotient.mk_sub,Submodule.Quotient.mk_eq_zero]
  change seqMap (involutionHom K) c.val-c.val ∈ bcoboundaries K q
  have he : seqMap (involutionHom K) c.val-c.val=(fun j => tr K j (c.val j)) := by
    funext j
    have hn : -(c.val j)=c.val j := (eq_neg_iff_add_eq_zero.mpr (two_eq_zero_of_mod (c.val j))).symm
    change K.t j (c.val j)-c.val j=c.val j+K.t j (c.val j)
    rw [sub_eq_add_neg,hn,add_comm]
  rw [he]
  exact transfer_boundary K q c

end
end Finsler.BorelInvolutionHomotopy
