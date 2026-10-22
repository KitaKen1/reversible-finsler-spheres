module

public import Finsler.Topology.BorelFreeK

/-! The class of the second involution on iterated Borel cohomology. For an involutive complex
K with a second commuting involution s, an outer contraction is a family of linear maps q
commuting with the differential and with the first involution such that q(1 + s) + (1 + s)q = 1.
Applied componentwise it commutes with the Borel differential of K and preserves the
filtration, so it is a contraction of the transfer of the iterated complex, and the class v of
the second involution acts as zero on the Borel cohomology of the iterated complex. For the
relative cochains of a pair with two commuting involutions r and τ, a 0-cocycle π with
π + τ^*π = 1 and r^*π = π gives an outer contraction; this applies to the indicator of a closed
and open set exchanged with its complement by τ and preserved by r. -/

@[expose] public section

namespace Finsler.BorelFreeV

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelIterate Finsler.BorelFree Finsler.BorelFreeK

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Algebra

variable {K : InvComplex}

/-- A contraction of the transfer of the second involution which commutes with the differential
and with the first involution. -/
structure OuterContraction (S : Commuting K) where
  q : (j : ℕ) → K.C j →ₗ[ZMod 2] K.C j
  comm_d : ∀ j x, K.d j (q j x) = q (j + 1) (K.d j x)
  comm_t : ∀ j x, K.t j (q j x) = q j (K.t j x)
  homotopy : ∀ j x, q j (x + S.s j x) + (q j x + S.s j (q j x)) = x

variable {S : Commuting K} (h : OuterContraction S)

/-- The outer contraction applied componentwise. -/
def oSeq : Seq K →ₗ[ZMod 2] Seq K := LinearMap.pi fun j => h.q j ∘ₗ LinearMap.proj j

theorem oSeq_apply (c : Seq K) (j : ℕ) : oSeq h c j = h.q j (c j) := rfl

theorem oSeq_low {k : ℕ} {c : Seq K} (hc : c ∈ low K k) : oSeq h c ∈ low K k := by
  intro j hj
  rw [oSeq_apply, hc j hj, map_zero]

theorem tr_q (j : ℕ) (x : K.C j) : tr K j (h.q j x) = h.q j (tr K j x) := by
  rw [tr_apply, tr_apply, map_add, h.comm_t]

/-- The componentwise outer contraction commutes with the Borel differential. -/
theorem D_oSeq (c : Seq K) : D K (oSeq h c) = oSeq h (D K c) := by
  funext j
  cases j with
  | zero => rw [D_zero, oSeq_apply, oSeq_apply, D_zero, tr_q]
  | succ j =>
    rw [D_succ, oSeq_apply, oSeq_apply, oSeq_apply, D_succ, map_add, h.comm_d, tr_q]

/-- The contraction of the transfer of the iterated complex from an outer contraction. -/
def toContraction : Contraction (borelInv S) where
  Q j := (oSeq h).restrict (fun _ hc => oSeq_low h hc)
  comm_d j x := seqOf_injective S _ (D_oSeq h (seqOf S j x))
  homotopy j x := by
    apply seqOf_injective S
    funext i
    exact h.homotopy i (seqOf S j x i)

include h in
/-- With an outer contraction, the class of the second involution acts as zero on the Borel
cohomology of the iterated complex. -/
theorem outerW_eq_zero (n : ℕ) (y : HR (borelInv S) n) : w (borelInv S) n y = 0 :=
  w_eq_zero (toContraction h) n y

end Algebra

section Pair

variable (P : TopPair.{0}) (r τ : P ⟶ P) (hr : r ≫ r = 𝟙 P) (hτ : τ ≫ τ = 𝟙 P)
  (hc : τ ≫ r = r ≫ τ) (π : singularCochainGroup (ZMod 2) P.fst 0)

/-- The outer contraction of the relative cochains of a pair with two commuting involutions r
and τ from a 0-cocycle π with π + τ^*π = 1 and r^*π = π. -/
def outerContraction (hδ : cochainCoboundary (ZMod 2) P.fst 0 π = 0)
    (hπ : π + cochainPullback (TopPair.Hom.fst τ) 0 π = cochainOne (R := ZMod 2) (Z := P.fst))
    (hrπ : cochainPullback (TopPair.Hom.fst r) 0 π = π) :
    OuterContraction (BorelInvariance.commuting hr τ hτ hc) where
  q j := (contraction P τ π hτ hδ hπ).Q j
  comm_d j x := (contraction P τ π hτ hδ hπ).comm_d j x
  comm_t j x := pullback_contraction_comm P τ r hτ π hδ hπ hrπ j x
    ((BorelInvariance.commuting hr τ hτ hc).st j x).symm
  homotopy j x := (contraction P τ π hτ hδ hπ).homotopy j x

/-- If the second involution of a pair exchanges a closed and open subset U of the space with
its complement and the first involution preserves U, the class of the second involution acts
as zero on the iterated Borel cohomology of the pair. -/
theorem outerW_eq_zero_of_isClopen (U : Set P.fst) (hU : IsClopen U)
    (hswap : ∀ x : P.fst, (TopPair.Hom.fst τ).hom x ∈ U ↔ x ∉ U)
    (hinv : ∀ x : P.fst, (TopPair.Hom.fst r).hom x ∈ U ↔ x ∈ U) (q : ℕ)
    (x : HR (borelInv (BorelInvariance.commuting hr τ hτ hc)) q) :
    w (borelInv (BorelInvariance.commuting hr τ hτ hc)) q x = 0 := by
  have hδ : cochainCoboundary (ZMod 2) P.fst 0
      (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) = 0 :=
    pointCochain_coboundary P.fst _ (fun σ x y => indicator_eq_of_isClopen P.fst hU σ x y)
  have hπ : pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2))) +
      cochainPullback (TopPair.Hom.fst τ) 0
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
  have hrπ : cochainPullback (TopPair.Hom.fst r) 0
      (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) =
      pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2))) := by
    rw [pointCochain_pullback]
    apply cochain_ext
    intro σ
    rw [pointCochain_eval, pointCochain_eval]
    by_cases hx : simplexPoint P.fst σ ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hinv _).mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hinv _).mp h))]
  exact outerW_eq_zero (outerContraction P r τ hr hτ hc _ hδ hπ hrπ) q x

end Pair

end

end Finsler.BorelFreeV
