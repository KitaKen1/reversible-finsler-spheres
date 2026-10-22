module

public import Finsler.Loop.CupCapOrder
public import Finsler.Topology.RelativeCapBoundary

/-! A pointwise localized two-cap source identity for a genuine
external-input component. No closedness or entire tensor cap map is
assumed; the actual intermediate carrier and degree casts are retained. -/

@[expose] public section
namespace Finsler.LocalizedCapCupComponentSource

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem cap_output_transport (X : TopCat.{0}) (a q q' N : ℕ)
    (hq : a + q = N) (hq' : a + q' = N) (hqq : q = q')
    (φ : singularCochainGroup (ZMod 2) X a) :
    absoluteChain X a q N hq φ ≫ eqToHom (congrArg (chains X).X hqq) =
      absoluteChain X a q' N hq' φ := by
  cases hqq
  simp only [eqToHom_refl, Category.comp_id]

theorem cap_cup_input (X : TopCat.{0}) (a b d q N : ℕ) (hd : a + b = d) (hN : N = d + q)
    (φ : singularCochainGroup (ZMod 2) X a) (ψ : singularCochainGroup (ZMod 2) X b) :
    absoluteChain X a (b + q) N (by omega) φ ≫ absoluteChain X b q (b + q) rfl ψ =
      absoluteChain X d q N hN.symm (CupOne.cup X a b d hd φ ψ) := by
  cases hN
  exact CupCapOrder.cap_cup X a b d q hd φ ψ

theorem component_source {X Y : TopCat.{0}} {κ : Type*} (U : κ → Set Y) (s : Y ⟶ X)
    {K E : ModuleCat.{0} (ZMod 2)} (a b d q N : ℕ) (hd : a + b = d) (hN : N = d + q)
    (φ : singularCochainGroup (ZMod 2) X a) (ψ : singularCochainGroup (ZMod 2) X b)
    (c : K ⟶ (small Y U).X (b + q)) (k : K ⟶ (chains X).X N)
    (g : (small Y U).X (b + q) ⟶ E) (j : E ⟶ (chains Y).X q)
    (hc : c ≫ (inclusion Y U).f (b + q) ≫ (push s).f (b + q) =
      k ≫ absoluteChain X a (b + q) N (by omega) φ)
    (hg : g ≫ j = (inclusion Y U).f (b + q) ≫
      absoluteChain Y b q (b + q) rfl (cochainPullback s b ψ)) :
    c ≫ g ≫ j ≫ (push s).f q = k ≫ absoluteChain X d q N hN.symm (CupOne.cup X a b d hd φ ψ) := by
  have hn := RelativeCapBoundary.absolute_chain_natural s b q (b + q) rfl ψ
  change absoluteChain Y b q (b + q) rfl (cochainPullback s b ψ) ≫ (push s).f q =
    (push s).f (b + q) ≫ absoluteChain X b q (b + q) rfl ψ at hn
  calc
    _ = c ≫ (inclusion Y U).f (b + q) ≫
        absoluteChain Y b q (b + q) rfl (cochainPullback s b ψ) ≫ (push s).f q := by
      rw [← Category.assoc g j, hg]
      simp only [Category.assoc]
    _ = (c ≫ (inclusion Y U).f (b + q) ≫ (push s).f (b + q)) ≫
        absoluteChain X b q (b + q) rfl ψ := by rw [hn]; simp only [Category.assoc]
    _ = k ≫ absoluteChain X d q N hN.symm (CupOne.cup X a b d hd φ ψ) := by
      rw [hc, Category.assoc, cap_cup_input X a b d q N hd hN]

end
end Finsler.LocalizedCapCupComponentSource
