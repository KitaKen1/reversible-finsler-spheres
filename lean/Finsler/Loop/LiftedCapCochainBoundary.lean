module

public import Finsler.Topology.SupportedCapCochain
public import Finsler.Topology.CapOutputSupport

/-! A real source-monic chain lift preserves the full cap/coboundary
identity. This applies to nonclosed cochains and bounded proper domains. -/

@[expose] public section
namespace Finsler.LiftedCapCochainBoundary

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem boundary {X : TopCat.{0}} {ι : Type*} (U : ι → Set X)
    (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j : K ⟶ chains X)
    (hj : ∀ q, Mono (j.f q)) (d : ℕ) (ξ : singularCochainGroup (ZMod 2) X d)
    (c : ∀ q, (small X U).X (d + q) ⟶ K.X q)
    (cδ : ∀ q, (small X U).X ((d + 1) + q) ⟶ K.X q)
    (hc : ∀ q, c q ≫ j.f q = (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl ξ)
    (hcδ : ∀ q, cδ q ≫ j.f q = (inclusion X U).f ((d + 1) + q) ≫
      absoluteChain X (d + 1) q ((d + 1) + q) rfl (cochainCoboundary (ZMod 2) X d ξ))
    (q : ℕ) :
    c (q + 1) ≫ K.d (q + 1) q =
      (small X U).d (d + (q + 1)) (d + q) ≫ c q -
      eqToHom (congrArg (small X U).X (show d + (q + 1) = (d + 1) + q by omega)) ≫ cδ q := by
  haveI := hj q
  apply (cancel_mono (j.f q)).mp
  simp only [Preadditive.sub_comp, Category.assoc]
  rw [← j.comm, ← Category.assoc, hc]
  have hb := SupportedCapCochain.absolute_coboundary X d q (d + q) rfl ξ
  have hb' : absoluteChain X d (q + 1) (d + (q + 1)) rfl ξ ≫ (chains X).d (q + 1) q =
      (chains X).d (d + (q + 1)) (d + q) ≫ absoluteChain X d q (d + q) rfl ξ -
      absoluteChain X (d + 1) q (d + (q + 1)) (by omega) (cochainCoboundary (ZMod 2) X d ξ) := by
    have aux (N : ℕ) (hN : N = d + q + 1) (h₀ : d + (q + 1) = N) (h₁ : (d + 1) + q = N) :
        absoluteChain X d (q + 1) N h₀ ξ ≫ (chains X).d (q + 1) q =
        (chains X).d N (d + q) ≫ absoluteChain X d q (d + q) rfl ξ -
          absoluteChain X (d + 1) q N h₁ (cochainCoboundary (ZMod 2) X d ξ) := by
      subst N
      exact hb
    exact aux _ (by omega) rfl (by omega)
  have hcast : eqToHom (congrArg (small X U).X (show d + (q + 1) = (d + 1) + q by omega)) ≫
      (inclusion X U).f ((d + 1) + q) ≫
        absoluteChain X (d + 1) q ((d + 1) + q) rfl (cochainCoboundary (ZMod 2) X d ξ) =
      (inclusion X U).f (d + (q + 1)) ≫
        absoluteChain X (d + 1) q (d + (q + 1)) (by omega) (cochainCoboundary (ZMod 2) X d ξ) := by
    have he : ∀ (N : ℕ) (hN : N = (d + 1) + q),
        eqToHom (congrArg (small X U).X hN) ≫ (inclusion X U).f ((d + 1) + q) ≫
          absoluteChain X (d + 1) q ((d + 1) + q) rfl (cochainCoboundary (ZMod 2) X d ξ) =
        (inclusion X U).f N ≫ absoluteChain X (d + 1) q N (by omega) (cochainCoboundary (ZMod 2) X d ξ) := by
      intro N hN
      subst N
      simp only [eqToHom_refl, Category.id_comp]
    exact he _ (by omega)
  rw [hc, hcδ]
  rw [Category.assoc, hb']
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
  rw [hcast]
  rw [← Category.assoc ((inclusion X U).f (d + (q + 1))), (inclusion X U).comm]
  simp only [Category.assoc]

end
end Finsler.LiftedCapCochainBoundary
