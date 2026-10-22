module

public import Finsler.Topology.TubeCochainExtension
public import Finsler.Topology.PartialDoubleCap

/-! The original localized supported Thom cap followed by the genuine
tested cap is the unique domain lift of the actual successive ambient
caps with the tested cochain extended by zero. The full supported cut
retains its actual small-chain retraction. -/

@[expose] public section
namespace Finsler.SupportedDoubleCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (X : TopCat.{0}) (A D : Set X) (k p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X k)
  (hφ : cochainPullback (SupportedCap.subspaceMap X A) k φ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) p)

def localized (q N : ℕ) (hN : k + (p + q) = N) :
    (small X (SupportedCap.cover X A D)).X N ⟶ (chains (TopCat.of D)).X q :=
  SupportedCap.localizedCap X A D k (p + q) N hN φ hφ ≫
    absoluteChain (TopCat.of D) p q (p + q) rfl ψ

theorem localized_inclusion (q N : ℕ) (hN : k + (p + q) = N) :
    localized X A D k p φ hφ ψ q N hN ≫ (push (SupportedCap.subspaceMap X D)).f q =
      (inclusion X (SupportedCap.cover X A D)).f N ≫
        absoluteChain X k (p + q) N hN φ ≫
        absoluteChain X p q (p + q) rfl (TubeCochainExtension.extend X D p ψ) := by
  have hn : absoluteChain (TopCat.of D) p q (p + q) rfl ψ ≫
      (push (SupportedCap.subspaceMap X D)).f q =
      (push (SupportedCap.subspaceMap X D)).f (p + q) ≫
        absoluteChain X p q (p + q) rfl (TubeCochainExtension.extend X D p ψ) := by
    simpa only [TubeCochainExtension.restriction, push] using
      RelativeCapBoundary.absolute_chain_natural (SupportedCap.subspaceMap X D) p q (p + q) rfl
        (TubeCochainExtension.extend X D p ψ)
  unfold localized
  rw [Category.assoc, hn, ← Category.assoc]
  have hl := SupportedCap.localizedCap_inclusion X A D k (p + q) N hN φ hφ
  simpa only [push, Category.assoc] using congrArg
    (fun t => t ≫ absoluteChain X p q (p + q) rfl (TubeCochainExtension.extend X D p ψ)) hl

theorem on_refinement {ι : Type*} (W : ι → Set X)
    (e : small X W ⟶ small X (SupportedCap.cover X A D))
    (he : e ≫ inclusion X (SupportedCap.cover X A D) = inclusion X W)
    (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
      (TopCat.toSSet.obj X).ιChainComplex σ.val ≫
        PartialDoubleCap.cap X k p q φ (TubeCochainExtension.extend X D p ψ) ≠ 0 →
          Set.range (X.toSSetObjEquiv _ σ.val) ⊆ D) (q : ℕ) :
    e.f (k + (p + q)) ≫ localized X A D k p φ hφ ψ q (k + (p + q)) rfl =
      PartialDoubleCap.localized X W D k p φ (TubeCochainExtension.extend X D p ψ) hgood q := by
  haveI : Mono ((push (SupportedCap.subspaceMap X D)).f q) := SupportedCap.subspacePush_mono X D q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X D)).f q)).mp
  rw [Category.assoc, localized_inclusion, PartialDoubleCap.localized_inclusion]
  have hi : e.f (k + (p + q)) ≫ (inclusion X (SupportedCap.cover X A D)).f (k + (p + q)) =
      (inclusion X W).f (k + (p + q)) := congrArg (fun f => f.f (k + (p + q))) he
  simpa only [PartialDoubleCap.cap, Category.assoc] using congrArg
    (fun t => t ≫ PartialDoubleCap.cap X k p q φ (TubeCochainExtension.extend X D p ψ)) hi

variable (hA : IsOpen A) (hD : IsOpen D) (hcover : A ∪ D = Set.univ)

def cut (q N : ℕ) (hN : k + (p + q) = N) : (chains X).X N ⟶ (chains (TopCat.of D)).X q :=
  SupportedCap.cut X A D hA hD hcover k (p + q) N hN φ hφ ≫
    absoluteChain (TopCat.of D) p q (p + q) rfl ψ

theorem cut_eq_localized (q N : ℕ) (hN : k + (p + q) = N) :
    cut X A D k p φ hφ ψ hA hD hcover q N hN =
      (TauCeti.smallSingularRetraction coeff (SupportedCap.cover X A D)
        (SupportedCap.cover_open X A D hA hD) (SupportedCap.cover_univ X A D hcover)).f N ≫
      localized X A D k p φ hφ ψ q N hN := by
  simp only [cut, localized, SupportedCap.cut, Category.assoc]

theorem cut_inclusion (q N : ℕ) (hN : k + (p + q) = N) :
    cut X A D k p φ hφ ψ hA hD hcover q N hN ≫ (push (SupportedCap.subspaceMap X D)).f q =
      (TauCeti.singularSmallApprox coeff (SupportedCap.cover X A D)).f N ≫
        absoluteChain X k (p + q) N hN φ ≫
        absoluteChain X p q (p + q) rfl (TubeCochainExtension.extend X D p ψ) := by
  rw [cut_eq_localized, Category.assoc, localized_inclusion]
  have hi := congrArg (fun f => f.f N)
    (TauCeti.smallSingularRetraction_comp_ι coeff (SupportedCap.cover X A D)
      (SupportedCap.cover_open X A D hA hD) (SupportedCap.cover_univ X A D hcover))
  simpa only [HomologicalComplex.comp_f, Category.assoc] using congrArg
    (fun t => t ≫ absoluteChain X k (p + q) N hN φ ≫
      absoluteChain X p q (p + q) rfl (TubeCochainExtension.extend X D p ψ)) hi

theorem cut_on_small {Z : TopCat.{0}} {ι : Type*} (W : ι → Set Z) (f : Z ⟶ X)
    (e : small Z W ⟶ small X (SupportedCap.cover X A D))
    (he : e ≫ inclusion X (SupportedCap.cover X A D) = inclusion Z W ≫ push f)
    (q N : ℕ) (hN : k + (p + q) = N) :
    (inclusion Z W).f N ≫ (push f).f N ≫ cut X A D k p φ hφ ψ hA hD hcover q N hN =
      e.f N ≫ localized X A D k p φ hφ ψ q N hN := by
  let r := TauCeti.smallSingularRetraction coeff (SupportedCap.cover X A D)
    (SupportedCap.cover_open X A D hA hD) (SupportedCap.cover_univ X A D hcover)
  have hr : inclusion X (SupportedCap.cover X A D) ≫ r = 𝟙 _ :=
    TauCeti.ι_comp_smallSingularRetraction coeff (SupportedCap.cover X A D)
      (SupportedCap.cover_open X A D hA hD) (SupportedCap.cover_univ X A D hcover)
  have hi : (inclusion Z W ≫ push f) ≫ r = e := by
    rw [← he, Category.assoc, hr, Category.comp_id]
  rw [cut_eq_localized]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun g => g.f N ≫ localized X A D k p φ hφ ψ q N hN) hi

end
end Finsler.SupportedDoubleCap
