module

public import Finsler.Loop.LiftedCapCochainBoundary
public import Finsler.Topology.DegreeLoweringExact

/-! An actual supported representative primitive compares two genuine
cap lifts inside any chain-monic target, including a closed carrier.
The primitive cap itself must land in that target; only chain monicity
is cancelled. All output degrees, including zero, are covered. -/

@[expose] public section
namespace Finsler.LiftedRepresentativeComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set X)
  (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j : K ⟶ chains X) (hj : ∀ q, Mono (j.f q))
  (d : ℕ) (φ ψ : singularCochainGroup (ZMod 2) X (d + 1)) (ξ : singularCochainGroup (ZMod 2) X d)
  (hδ : cochainCoboundary (ZMod 2) X d ξ = φ - ψ)
  (f g : DegreeLoweringHomology.Map (small X U) K (d + 1))
  (hf : ∀ q, f.component q ≫ j.f q = (inclusion X U).f ((d + 1) + q) ≫ absoluteChain X (d + 1) q ((d + 1) + q) rfl φ)
  (hg : ∀ q, g.component q ≫ j.f q = (inclusion X U).f ((d + 1) + q) ≫ absoluteChain X (d + 1) q ((d + 1) + q) rfl ψ)
  (c : ∀ q, (small X U).X (d + q) ⟶ K.X q)
  (hc : ∀ q, c q ≫ j.f q = (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl ξ)

def primitive (q : ℕ) : (small X U).X ((d + 1) + q) ⟶ K.X (q + 1) :=
  eqToHom (congrArg (small X U).X (show (d + 1) + q = d + (q + 1) by omega)) ≫ c (q + 1)

include hc in
theorem primitive_source (q : ℕ) : primitive X U K d c q ≫ j.f (q + 1) =
    (inclusion X U).f ((d + 1) + q) ≫ absoluteChain X d (q + 1) ((d + 1) + q) (by omega) ξ := by
  dsimp only [primitive]
  rw [Category.assoc, hc]
  have aux (N : ℕ) (hN : N = d + (q + 1)) :
      eqToHom (congrArg (small X U).X hN) ≫ (inclusion X U).f (d + (q + 1)) ≫
        absoluteChain X d (q + 1) (d + (q + 1)) rfl ξ =
      (inclusion X U).f N ≫ absoluteChain X d (q + 1) N (by omega) ξ := by
    subst N
    simp only [eqToHom_refl, Category.id_comp]
  exact aux ((d + 1) + q) (by omega)

theorem native_boundary (q : ℕ) :
    absoluteChain X d (q + 1) ((d + 1) + q) (by omega) ξ ≫ (chains X).d (q + 1) q =
      (chains X).d ((d + 1) + q) (d + q) ≫ absoluteChain X d q (d + q) rfl ξ -
        absoluteChain X (d + 1) q ((d + 1) + q) rfl (cochainCoboundary (ZMod 2) X d ξ) := by
  have hb := SupportedCapCochain.absolute_coboundary X d q (d + q) rfl ξ
  have aux (N : ℕ) (hN : N = d + q + 1) (h₀ : d + (q + 1) = N) (h₁ : (d + 1) + q = N) :
      absoluteChain X d (q + 1) N h₀ ξ ≫ (chains X).d (q + 1) q =
        (chains X).d N (d + q) ≫ absoluteChain X d q (d + q) rfl ξ -
          absoluteChain X (d + 1) q N h₁ (cochainCoboundary (ZMod 2) X d ξ) := by
    subst N
    exact hb
  exact aux _ (by omega) (by omega) rfl

include hj hδ hf hg hc in
theorem cycle_boundary (q : ℕ) :
    (small X U).iCycles ((d + 1) + q) ≫ (f.component q - g.component q) =
      ((small X U).iCycles ((d + 1) + q) ≫ (-primitive X U K d c q)) ≫ K.d (q + 1) q := by
  have hz : ((small X U).iCycles ((d + 1) + q) ≫ (inclusion X U).f ((d + 1) + q)) ≫
      (chains X).d ((d + 1) + q) (d + q) = 0 := by
    rw [Category.assoc, (inclusion X U).comm, ← Category.assoc, (small X U).iCycles_d, zero_comp]
  have he := congrArg (fun z => (small X U).iCycles ((d + 1) + q) ≫ (inclusion X U).f ((d + 1) + q) ≫ z)
    (native_boundary X d ξ q)
  rw [hδ, SupportedCapCochain.absolute_sub] at he
  simp only [Preadditive.comp_sub, ← Category.assoc, hz, zero_comp, zero_sub] at he
  have : Mono (j.f q) := hj q
  apply (cancel_mono (j.f q)).mp
  simp only [Preadditive.sub_comp, Category.assoc]
  rw [hf, hg, ← j.comm]
  simp only [Preadditive.comp_sub, Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
  rw [← Category.assoc (primitive X U K d c q), primitive_source X U K j d ξ c hc q]
  simpa only [Preadditive.comp_sub, Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc, neg_neg] using (congrArg Neg.neg he).symm

include hj hδ hf hg hc in
theorem homology_eq (q : ℕ) : f.homology q = g.homology q :=
  DegreeLoweringExact.homology_eq_of_cycle_boundary f g q (-primitive X U K d c q)
    (cycle_boundary X U K j hj d φ ψ ξ hδ f g hf hg c hc q)

end
end Finsler.LiftedRepresentativeComparison
