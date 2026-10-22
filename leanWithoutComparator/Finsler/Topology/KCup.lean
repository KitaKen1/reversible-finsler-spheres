module

public import Finsler.Topology.GradedDelta
public import Finsler.Topology.BorelInvariance
public import Finsler.Topology.BasisBudget
public import Finsler.Topology.BorelFreeK

/-! Cup products on K-Borel cohomology (iterated Borel cohomology).

A degree-p graded map A of an involutive complex K which commutes with a second involution S
(`Commuting K`) acts componentwise on the t-Borel cochains, which are the cochains of the
involutive complex `borelInv S`; this is a graded map of `borelInv S`, and forgetting S
(`BasisBudget.fgtR`) intertwines its action on K-Borel cohomology with the action of A on
reflection Borel cohomology. For a pair with two commuting involutions and a cocycle strictly
invariant under both, the relative cup with the cocycle is such a map: this is the K-Borel cup
with a K-invariant absolute class, lifting the reflection Borel cup `BorelCup.cup`. -/

@[expose] public section

namespace Finsler.KCup

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair Finsler.BorelGraded
open Finsler.BorelIterate Finsler.GradedDelta Finsler.BasisBudget Finsler.BorelFreeK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Lift

variable {K : InvComplex} (S : Commuting K) {p : ℕ} (A : Map K K p)
  (hA : ∀ j x, S.s (p + j) (A.f j x) = A.f j (S.s j x))

theorem castC_s {a b : ℕ} (h : a = b) (x : K.C a) : S.s b (castC K h x) = castC K h (S.s a x) := by
  subst h
  rfl

include hA in
theorem total_seqS (c : Seq K) : seqS S (total A c) = total A (seqS S c) := by
  funext j
  rw [seqS_apply, total_apply, total_apply]
  by_cases h : p ≤ j
  · rw [dif_pos h, dif_pos h, castC_s, hA]
    rfl
  · rw [dif_neg h, dif_neg h, map_zero]

include hA in
/-- The graded map on the t-Borel complex. -/
def liftMap : Map (borelInv S) (borelInv S) p where
  f j := (total A).restrict (fun c hc => total_low A hc)
  comm_d j x := by
    apply seqOf_injective S
    rw [seqOf_castC]
    exact total_D A (seqOf S j x)
  comm_t j x := seqOf_injective S _ (total_seqS S A hA (seqOf S j x))

/-- Forgetting the action commutes with graded maps. -/
theorem forget_onHR {L M : InvComplex} {q₀ : ℕ} (B : Map L M q₀) (q : ℕ) (x : HR L q) :
    BorelCochain.forget M (q₀ + q) (onHR B q x) = onH B q (BorelCochain.forget L q x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (forgetCocycle M (q₀ + q) (cyclesMap B q c)) =
    Submodule.Quotient.mk (cocMap B q (forgetCocycle L q c))
  congr 1
  apply Subtype.ext
  exact total_at B (c : Seq L) q

theorem cohomologyEquiv_onH (q : ℕ) (y : H (borelInv S) q) :
    cohomologyEquiv S (p + q) (onH (liftMap S A hA) q y) = onHR A q (cohomologyEquiv S q y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

/-- **The K-Borel action is compatible with forgetting the second involution.** -/
theorem fgtR_lift (q : ℕ) (y : HR (borelInv S) q) :
    fgtR S (p + q) (onHR (liftMap S A hA) q y) = onHR A q (fgtR S q y) := by
  rw [fgtR_apply, fgtR_apply, forget_onHR, cohomologyEquiv_onH]

end Lift

/-! ### The K-Borel cup with an invariant cocycle -/

section Pair

variable (P : TopPair.{0}) {r τ : P ⟶ P} (hr : r ≫ r = 𝟙 P) (hτ : τ ≫ τ = 𝟙 P)
  (hc : τ ≫ r = r ≫ τ) {p : ℕ} (α : singularCochainGroup (ZMod 2) P.fst p)
  (hα : cochainCoboundary (ZMod 2) P.fst p α = 0)
  (hir : cochainPullback (TopPair.Hom.fst r) p α = α)
  (hiτ : cochainPullback (TopPair.Hom.fst τ) p α = α)

include hiτ in
theorem cup_comm_s (j : ℕ) (x : (ofPair P r hr).C j) :
    (Finsler.BorelInvariance.commuting hr τ hτ hc).s (p + j)
        ((BorelCup.gradedCup P r hr p α hα hir).f j x) =
      (BorelCup.gradedCup P r hr p α hα hir).f j
        ((Finsler.BorelInvariance.commuting hr τ hτ hc).s j x) := by
  change RelativeCupCochain.pullback τ (p + j) (RelativeCupCochain.cup P p j α x) =
    RelativeCupCochain.cup P p j α (RelativeCupCochain.pullback τ j x)
  rw [RelativeCupCochain.naturality, hiτ]

/-- **The K-Borel cup with a cocycle invariant under both involutions.** -/
def kcup (q : ℕ) :
    HR (borelInv (Finsler.BorelInvariance.commuting hr τ hτ hc)) q →ₗ[ZMod 2]
      HR (borelInv (Finsler.BorelInvariance.commuting hr τ hτ hc)) (p + q) :=
  onHR (liftMap (Finsler.BorelInvariance.commuting hr τ hτ hc)
    (BorelCup.gradedCup P r hr p α hα hir) (cup_comm_s P hr hτ hc α hα hir hiτ)) q

/-- Forgetting the half rotation takes the K-Borel cup to the reflection Borel cup. -/
theorem fgtR_kcup (q : ℕ) (y : HR (borelInv (Finsler.BorelInvariance.commuting hr τ hτ hc)) q) :
    fgtR (Finsler.BorelInvariance.commuting hr τ hτ hc) (p + q) (kcup P hr hτ hc α hα hir hiτ q y) =
      BorelCup.cup P r hr p α hα hir q
        (fgtR (Finsler.BorelInvariance.commuting hr τ hτ hc) q y) :=
  fgtR_lift _ _ _ q y

end Pair

end

end Finsler.KCup
