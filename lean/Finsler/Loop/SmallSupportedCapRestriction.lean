module

public import Finsler.Topology.SmallRetractionComparison

/-! On actual mapped small chains, the canonical supported-cap
subdivision is literally fixed. A genuine subspace cap lift therefore
equals that supported cap after its actual neighborhood map, using
chain monicity only in the canonical neighborhood. -/

@[expose] public section
namespace Finsler.SmallSupportedCapRestriction

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem approximation_fixed {X Y : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set Y) (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    inclusion X U ≫ push f ≫ TauCeti.singularSmallApprox coeff V = inclusion X U ≫ push f := by
  calc
    _ = (SmallRetractionComparison.map U V f r hf ≫ inclusion Y V) ≫
        TauCeti.singularSmallApprox coeff V := by
      rw [SmallRetractionComparison.map_inclusion, Category.assoc]
    _ = SmallRetractionComparison.map U V f r hf ≫ inclusion Y V := by
      rw [Category.assoc, TauCeti.ι_comp_singularSmallApprox]
    _ = _ := SmallRetractionComparison.map_inclusion U V f r hf

theorem component {X Y : TopCat.{0}} {ι : Type*} (U : ι → Set X) (f : X ⟶ Y)
    (A B : Set Y) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
    (r : ι → Bool) (hf : ∀ i, Set.MapsTo f (U i) (SupportedCap.cover Y A B (r i)))
    (D : Set X) {κ : Type*} (V : κ → Set (TopCat.of D))
    (g : TopCat.of D ⟶ TopCat.of B)
    (hg : g ≫ SupportedCap.subspaceMap Y B = SupportedCap.subspaceMap X D ≫ f)
    (d q : ℕ) (φ : singularCochainGroup (ZMod 2) Y d)
    (hs : cochainPullback (SupportedCap.subspaceMap Y A) d φ = 0)
    (c : (small X U).X (d + q) ⟶ (small (TopCat.of D) V).X q)
    (hcap : c ≫ (inclusion (TopCat.of D) V ≫ push (SupportedCap.subspaceMap X D)).f q =
      (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl (cochainPullback f d φ)) :
    c ≫ (inclusion (TopCat.of D) V).f q ≫ (push g).f q =
      (inclusion X U).f (d + q) ≫ (push f).f (d + q) ≫
        SupportedCap.cut Y A B hA hB hc d q (d + q) rfl φ hs := by
  haveI : Mono ((push (SupportedCap.subspaceMap Y B)).f q) := SupportedCap.subspacePush_mono Y B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap Y B)).f q)).mp
  have hgp := congrArg (fun k => (push k).f q) hg
  simp only [push_comp, HomologicalComplex.comp_f] at hgp
  have hfix := congrArg (fun k => k.f (d + q))
    (approximation_fixed U (SupportedCap.cover Y A B) f r hf)
  simp only [HomologicalComplex.comp_f] at hfix
  have hn := RelativeCapBoundary.absolute_chain_natural f d q (d + q) rfl φ
  change absoluteChain X d q (d + q) rfl (cochainPullback f d φ) ≫ (push f).f q =
    (push f).f (d + q) ≫ absoluteChain Y d q (d + q) rfl φ at hn
  have hcut := SupportedCap.cut_inclusion Y A B hA hB hc d q (d + q) rfl φ hs
  change SupportedCap.cut Y A B hA hB hc d q (d + q) rfl φ hs ≫
    (push (SupportedCap.subspaceMap Y B)).f q =
    (TauCeti.singularSmallApprox coeff (SupportedCap.cover Y A B)).f (d + q) ≫
      absoluteChain Y d q (d + q) rfl φ at hcut
  calc
    _ = c ≫ (inclusion (TopCat.of D) V).f q ≫
        (push (SupportedCap.subspaceMap X D)).f q ≫ (push f).f q := by
      simpa only [Category.assoc] using congrArg
        (fun k => c ≫ (inclusion (TopCat.of D) V).f q ≫ k) hgp
    _ = (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl
        (cochainPullback f d φ) ≫ (push f).f q := by
      simpa only [HomologicalComplex.comp_f, Category.assoc] using
        congrArg (fun k => k ≫ (push f).f q) hcap
    _ = (inclusion X U).f (d + q) ≫ (push f).f (d + q) ≫
        absoluteChain Y d q (d + q) rfl φ := by
      simpa only [Category.assoc] using congrArg (fun k => (inclusion X U).f (d + q) ≫ k) hn
    _ = (inclusion X U).f (d + q) ≫ (push f).f (d + q) ≫
        (TauCeti.singularSmallApprox coeff (SupportedCap.cover Y A B)).f (d + q) ≫
        absoluteChain Y d q (d + q) rfl φ := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ absoluteChain Y d q (d + q) rfl φ) hfix.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun k => (inclusion X U).f (d + q) ≫ (push f).f (d + q) ≫ k) hcut.symm

end
end Finsler.SmallSupportedCapRestriction
