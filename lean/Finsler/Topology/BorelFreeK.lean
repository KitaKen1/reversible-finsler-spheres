module

public import Finsler.Topology.BorelFree
public import Finsler.Topology.BorelInvariance
public import Finsler.Topology.BorelHomotopy

/-! The reflection class on iterated Borel cohomology. For an involutive complex K with a
second commuting involution s, the iterated complex has the Borel cochains of K of filtration
n + 1 in degree n. The inclusion of filtration n + 1 into filtration n + 2 is a degree-one map
of the iterated complex commuting with its differential and with s: it is the reflection class
w on the Borel cohomology of the iterated complex (the K-Borel cohomology), and it is natural
for maps commuting with the second involutions. If the transfer of K has a contraction
commuting with s, applying it componentwise is a homotopy from this map to zero which commutes
with s, so w acts as zero on the K-Borel cohomology. For the relative cochains of a pair with
two commuting involutions r and τ, a 0-cocycle π with π + r^*π = 1 and τ^*π = π gives such a
contraction; this applies to the indicator of a closed and open set exchanged with its
complement by r and preserved by τ. If all Borel cohomology of K vanishes, so does the Borel
cohomology of the iterated complex. The reflection class is also written with values in the
next degree. -/

@[expose] public section

namespace Finsler.BorelFreeK

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelIterate Finsler.BorelGraded Finsler.BorelFree

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Algebra

variable {K : InvComplex} (S : Commuting K)

/-- The underlying Borel cochain of a cochain of the iterated complex. -/
def seqOf (n : ℕ) (x : (borelInv S).C n) : Seq K := ((toLow S n x : low K (n + 1)) : Seq K)

theorem seqOf_injective (n : ℕ) : Function.Injective (seqOf S n) :=
  fun _ _ h => Subtype.ext h

theorem seqOf_castC {a b : ℕ} (h : a = b) (x : (borelInv S).C a) :
    seqOf S b (castC (borelInv S) h x) = seqOf S a x := by
  subst b
  rfl

theorem seqOf_d (n : ℕ) (x : (borelInv S).C n) :
    seqOf S (n + 1) ((borelInv S).d n x) = D K (seqOf S n x) := rfl

theorem seqOf_t (n : ℕ) (x : (borelInv S).C n) :
    seqOf S n ((borelInv S).t n x) = seqS S (seqOf S n x) := rfl

theorem seqOf_add (n : ℕ) (x y : (borelInv S).C n) :
    seqOf S n (x + y) = seqOf S n x + seqOf S n y := rfl

/-- If all Borel cohomology of an involutive complex vanishes, so does the Borel cohomology of
its iterated complex. -/
theorem HR_borelInv_eq_zero (h : ∀ (k : ℕ) (y : HR K k), y = 0) (q : ℕ)
    (z : HR (borelInv S) q) : z = 0 := by
  have hH : ∀ (k : ℕ) (y : H (borelInv S) k), y = 0 := fun k y => by
    apply (cohomologyEquiv S k).injective
    rw [h k (cohomologyEquiv S k y), map_zero]
  induction q with
  | zero =>
    apply BorelQuasiIso.forget_zero_injective (borelInv S)
    rw [hH 0 (forget _ 0 z), map_zero]
  | succ q ih =>
    obtain ⟨y, rfl⟩ := (exact_forget (borelInv S) q z).mp (hH (q + 1) _)
    rw [ih y, map_zero]

/-- The reflection class on the iterated complex: inclusion of the Borel cochains of
filtration j + 1 into those of filtration j + 2. -/
def innerW : BorelGraded.Map (borelInv S) (borelInv S) 1 where
  f j := Submodule.inclusion (low_mono K (show j + 1 ≤ 1 + j + 1 by omega))
  comm_d j x := by
    apply seqOf_injective S
    rw [seqOf_castC]
    rfl
  comm_t j x := seqOf_injective S _ rfl

theorem seqOf_innerW (j : ℕ) (x : (borelInv S).C j) :
    seqOf S (1 + j) ((innerW S).f j x) = seqOf S j x := rfl

variable (h : Contraction K) (hs : ∀ j x, S.s j (h.Q j x) = h.Q j (S.s j x))

/-- The contraction applied to the Borel cochains of a given filtration. -/
def qLow (j : ℕ) : (borelInv S).C j →ₗ[ZMod 2] (borelInv S).C j :=
  (qSeq h).restrict (fun _ hc => qSeq_low h hc)

theorem seqOf_qLow (j : ℕ) (x : (borelInv S).C j) :
    seqOf S j (qLow S h j x) = qSeq h (seqOf S j x) := rfl

include hs in
theorem seqS_qSeq (c : Seq K) : seqS S (qSeq h c) = qSeq h (seqS S c) := by
  funext j
  exact hs j (c j)

/-- The homotopy family of the contraction on the iterated complex. -/
def family : BorelHomotopy.Family (borelInv S) (borelInv S) 0 where
  f j := castC (borelInv S) (Nat.zero_add j).symm ∘ₗ qLow S h j
  comm_t j x := by
    apply seqOf_injective S
    change seqOf S (0 + j) ((borelInv S).t (0 + j)
        (castC (borelInv S) (Nat.zero_add j).symm (qLow S h j x))) =
      seqOf S (0 + j) (castC (borelInv S) (Nat.zero_add j).symm
        (qLow S h j ((borelInv S).t j x)))
    rw [seqOf_t, seqOf_castC, seqOf_castC, seqOf_qLow, seqOf_qLow, seqOf_t]
    exact seqS_qSeq S h hs _

theorem seqOf_family (j : ℕ) (x : (borelInv S).C j) :
    seqOf S (0 + j) ((family S h hs).f j x) = qSeq h (seqOf S j x) := by
  change seqOf S (0 + j) (castC (borelInv S) (Nat.zero_add j).symm (qLow S h j x)) = _
  rw [seqOf_castC]
  rfl

include h hs in
/-- With a contraction of the transfer commuting with the second involution, the reflection
class acts as zero on the Borel cohomology of the iterated complex. -/
theorem innerW_eq_zero (q : ℕ) (x : HR (borelInv S) q) :
    BorelGraded.onHR (innerW S) q x = 0 := by
  refine BorelHomotopy.onHR_zero (family S h hs) (innerW S) (fun j y => ?_) q x
  apply seqOf_injective S
  rw [seqOf_d, seqOf_family, D_qSeq, seqOf_add, seqOf_castC, seqOf_castC, seqOf_innerW,
    seqOf_family, seqOf_d]

end Algebra

section Natural

variable {K L : InvComplex} {SK : Commuting K} {SL : Commuting L} (Φ : CommHom SK SL)

/-- The reflection class of the iterated complex is natural for maps commuting with the second
involutions, on total cochains. -/
theorem seqMap_total_innerW (c : Seq (borelInv SK)) :
    seqMap (borelHom Φ) (BorelGraded.total (innerW SK) c) =
      BorelGraded.total (innerW SL) (seqMap (borelHom Φ) c) := by
  funext j
  by_cases hj : 1 ≤ j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [seqMap_apply, BorelGraded.total_at, BorelGraded.total_at, seqMap_apply]
    exact seqOf_injective SL _ rfl
  · have h0 : j < 1 := by omega
    rw [seqMap_apply, BorelGraded.total_below _ _ h0, BorelGraded.total_below _ _ h0, map_zero]

/-- The reflection class on K-Borel cohomology is natural. -/
theorem innerW_natural (q : ℕ) (x : HR (borelInv SK) q) :
    HRmap (borelHom Φ) (1 + q) (BorelGraded.onHR (innerW SK) q x) =
      BorelGraded.onHR (innerW SL) q (HRmap (borelHom Φ) q x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (Submodule.Quotient.mk (bcocycleMap (borelHom Φ) (1 + q)
      (BorelGraded.cyclesMap (innerW SK) q c)) : HR (borelInv SL) (1 + q)) =
    Submodule.Quotient.mk (BorelGraded.cyclesMap (innerW SL) q (bcocycleMap (borelHom Φ) q c))
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact seqMap_total_innerW Φ (c : Seq (borelInv SK))

/-- Maps of involutive complexes commute with the change of degree along an equality. -/
theorem HRmap_castHR {K L : InvComplex} (φ : InvHom K L) {a b : ℕ} (h : a = b) (x : HR K a) :
    HRmap φ b (castHR h x) = castHR h (HRmap φ a x) := by
  subst b
  rfl

/-- The reflection class on the Borel cohomology of the iterated complex, with values in
degree q + 1. -/
def innerStep (S : Commuting K) (q : ℕ) : HR (borelInv S) q →ₗ[ZMod 2] HR (borelInv S) (q + 1) :=
  castHR (Nat.add_comm 1 q) ∘ₗ onHR (innerW S) q

theorem innerStep_apply (S : Commuting K) (q : ℕ) (x : HR (borelInv S) q) :
    innerStep S q x = castHR (Nat.add_comm 1 q) (onHR (innerW S) q x) := rfl

/-- The reflection class with values in the next degree is natural. -/
theorem HRmap_innerStep (q : ℕ) (x : HR (borelInv SK) q) :
    HRmap (borelHom Φ) (q + 1) (innerStep SK q x) =
      innerStep SL q (HRmap (borelHom Φ) q x) := by
  rw [innerStep_apply, innerStep_apply, HRmap_castHR, innerW_natural]

/-- The vanishing of the reflection class is transported backwards along a map which is
injective in the next degree. -/
theorem innerW_zero_of_injective (q : ℕ)
    (hinj : Function.Injective (HRmap (borelHom Φ) (1 + q)))
    (h : ∀ y : HR (borelInv SL) q, BorelGraded.onHR (innerW SL) q y = 0)
    (x : HR (borelInv SK) q) : BorelGraded.onHR (innerW SK) q x = 0 := by
  apply hinj
  rw [innerW_natural, h, map_zero]

/-- The vanishing of the reflection class is transported forwards along a surjective map. -/
theorem innerW_zero_of_surjective (q : ℕ) (hsurj : Function.Surjective (HRmap (borelHom Φ) q))
    (h : ∀ x : HR (borelInv SK) q, BorelGraded.onHR (innerW SK) q x = 0)
    (y : HR (borelInv SL) q) : BorelGraded.onHR (innerW SL) q y = 0 := by
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← innerW_natural, h, map_zero]

end Natural

section Pair

variable (P : TopPair.{0}) (r τ : P ⟶ P) (hr : r ≫ r = 𝟙 P)
  (π : singularCochainGroup (ZMod 2) P.fst 0)

/-- If π is invariant under τ, multiplication by π followed by r^* commutes with τ^*, given
that r^* and τ^* commute. -/
theorem pullback_contraction_comm (hδ : cochainCoboundary (ZMod 2) P.fst 0 π = 0)
    (hπ : π + cochainPullback (TopPair.Hom.fst r) 0 π = cochainOne (R := ZMod 2) (Z := P.fst))
    (hτ : cochainPullback (TopPair.Hom.fst τ) 0 π = π) (j : ℕ)
    (x : RelativeCupCochain.relative P j)
    (hcomm : RelativeCupCochain.pullback τ j (RelativeCupCochain.pullback r j x) =
      RelativeCupCochain.pullback r j (RelativeCupCochain.pullback τ j x)) :
    RelativeCupCochain.pullback τ j ((contraction P r π hr hδ hπ).Q j x) =
      (contraction P r π hr hδ hπ).Q j (RelativeCupCochain.pullback τ j x) := by
  change RelativeCupCochain.pullback τ j (mul P π j (RelativeCupCochain.pullback r j x)) =
    mul P π j (RelativeCupCochain.pullback r j (RelativeCupCochain.pullback τ j x))
  rw [pullback_mul, hτ, hcomm]

/-- If the first involution of a pair exchanges a closed and open subset U of the space with
its complement and the second involution preserves U, the reflection class acts as zero on the
iterated Borel cohomology of the pair. -/
theorem innerW_eq_zero_of_isClopen (hτ : τ ≫ τ = 𝟙 P) (hc : τ ≫ r = r ≫ τ) (U : Set P.fst)
    (hU : IsClopen U) (hswap : ∀ x : P.fst, (TopPair.Hom.fst r).hom x ∈ U ↔ x ∉ U)
    (hinv : ∀ x : P.fst, (TopPair.Hom.fst τ).hom x ∈ U ↔ x ∈ U) (q : ℕ)
    (x : HR (borelInv (BorelInvariance.commuting hr τ hτ hc)) q) :
    BorelGraded.onHR (innerW (BorelInvariance.commuting hr τ hτ hc)) q x = 0 := by
  have hδ : cochainCoboundary (ZMod 2) P.fst 0
      (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) = 0 :=
    pointCochain_coboundary P.fst _ (fun σ x y => indicator_eq_of_isClopen P.fst hU σ x y)
  have hπ : pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2))) +
      cochainPullback (TopPair.Hom.fst r) 0
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
  have hτπ : cochainPullback (TopPair.Hom.fst τ) 0
      (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) =
      pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2))) := by
    rw [pointCochain_pullback]
    apply cochain_ext
    intro σ
    rw [pointCochain_eval, pointCochain_eval]
    by_cases hx : simplexPoint P.fst σ ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hinv _).mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hinv _).mp h))]
  exact innerW_eq_zero (BorelInvariance.commuting hr τ hτ hc)
    (contraction P r _ hr hδ hπ)
    (fun j y => pullback_contraction_comm P r τ hr _ hδ hπ hτπ j y
      ((BorelInvariance.commuting hr τ hτ hc).st j y)) q x

end Pair

end

end Finsler.BorelFreeK
