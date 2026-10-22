module

public import Finsler.Loop.CapCupNested
public import Finsler.Loop.DegreeLoweringComposition

/-! Exact source formula for an actual localized first cap followed
by a bounded second cap. No closure of the ambient second cochain is used. -/

@[expose] public section
namespace Finsler.LocalizedCapCupCompositionSource

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {X Y : TopCat.{0}} {ι κ : Type*} (V : ι → Set X) (U : κ → Set Y)
  (s : Y ⟶ X) {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (j : E ⟶ chains Y)
  {a b : ℕ} (φ : singularCochainGroup (ZMod 2) X a) (ψ : singularCochainGroup (ZMod 2) X b)
  (f : DegreeLoweringHomology.Map (small X V) (small Y U) a)
  (g : DegreeLoweringHomology.Map (small Y U) E b)
  (hf : ∀ q, f.component q ≫ (inclusion Y U).f q ≫ (push s).f q =
    (inclusion X V).f (a + q) ≫ absoluteChain X a q (a + q) rfl φ)
  (hg : ∀ q, g.component q ≫ j.f q = (inclusion Y U).f (b + q) ≫
    absoluteChain Y b q (b + q) rfl (cochainPullback s b ψ))

include hf hg in
theorem component_source (q : ℕ) :
    (DegreeLoweringComposition.compose f g).component q ≫ (j ≫ push s).f q =
      (inclusion X V).f ((a + b) + q) ≫
        absoluteChain X (a + b) q ((a + b) + q) rfl (cochainCup a b φ ψ) := by
  have hn := RelativeCapBoundary.absolute_chain_natural s b q (b + q) rfl ψ
  change absoluteChain Y b q (b + q) rfl (cochainPullback s b ψ) ≫ (push s).f q =
    (push s).f (b + q) ≫ absoluteChain X b q (b + q) rfl ψ at hn
  have ht := transport_f (inclusion X V) ((a + b) + q) (a + (b + q)) (Nat.add_assoc a b q)
  rw [DegreeLoweringComposition.component, HomologicalComplex.comp_f]
  calc
    _ = eqToHom (congrArg (small X V).X (Nat.add_assoc a b q)) ≫
        f.component (b + q) ≫ (inclusion Y U).f (b + q) ≫
          absoluteChain Y b q (b + q) rfl (cochainPullback s b ψ) ≫ (push s).f q := by
      simp only [Category.assoc]
      rw [← Category.assoc (g.component q), hg]
      simp only [Category.assoc]
    _ = eqToHom (congrArg (small X V).X (Nat.add_assoc a b q)) ≫
        (f.component (b + q) ≫ (inclusion Y U).f (b + q) ≫ (push s).f (b + q)) ≫
          absoluteChain X b q (b + q) rfl ψ := by
      simp only [Category.assoc]
      rw [hn]
    _ = (eqToHom (congrArg (small X V).X (Nat.add_assoc a b q)) ≫
        (inclusion X V).f (a + (b + q))) ≫
          PartialDoubleCap.cap X a b q φ ψ := by
      rw [hf]
      simp only [PartialDoubleCap.cap, Category.assoc]
    _ = (inclusion X V).f ((a + b) + q) ≫
        (eqToHom (congrArg (chains X).X (Nat.add_assoc a b q)) ≫ PartialDoubleCap.cap X a b q φ ψ) := by
      rw [ht, Category.assoc]
    _ = _ := by rw [← CapCupNested.flat_nested]

end
end Finsler.LocalizedCapCupCompositionSource
