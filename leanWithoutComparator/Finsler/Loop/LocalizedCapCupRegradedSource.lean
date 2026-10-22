module

public import Finsler.Loop.LocalizedCapCupCompositionSource
public import Finsler.Loop.DegreeLoweringRegrade

/-! The localized composition source formula in the precise native
cup degree convention used by the real interchange identity. -/

@[expose] public section
namespace Finsler.LocalizedCapCupRegradedSource

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem component_source {X Y : TopCat.{0}} {ι κ : Type*} (V : ι → Set X) (U : κ → Set Y)
    (s : Y ⟶ X) {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (j : E ⟶ chains Y)
    {a b : ℕ} (φ : singularCochainGroup (ZMod 2) X a) (ψ : singularCochainGroup (ZMod 2) X b)
    (f : DegreeLoweringHomology.Map (small X V) (small Y U) a)
    (g : DegreeLoweringHomology.Map (small Y U) E b)
    (hf : ∀ q, f.component q ≫ (inclusion Y U).f q ≫ (push s).f q =
      (inclusion X V).f (a + q) ≫ absoluteChain X a q (a + q) rfl φ)
    (hg : ∀ q, g.component q ≫ j.f q = (inclusion Y U).f (b + q) ≫
      absoluteChain Y b q (b + q) rfl (cochainPullback s b ψ))
    (d : ℕ) (hd : a + b = d) (q : ℕ) :
    (DegreeLoweringRegrade.regrade (DegreeLoweringComposition.compose f g) d hd.symm).component q ≫
      (j ≫ push s).f q = (inclusion X V).f (d + q) ≫
        absoluteChain X d q (d + q) rfl (CupOne.cup X a b d hd φ ψ) := by
  subst d
  simpa only [DegreeLoweringRegrade.regrade, eqToHom_refl, Category.id_comp,
    CupOne.cup_comparison] using
    LocalizedCapCupCompositionSource.component_source V U s j φ ψ f g hf hg q

end
end Finsler.LocalizedCapCupRegradedSource
