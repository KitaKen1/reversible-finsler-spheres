module

public import Finsler.Topology.SupportedDoubleCap
public import Finsler.Topology.SmallCoverRefinement

/-! On every actual adequate refinement, the original localized
supported double cap agrees literally with any actual domain lift of
the specified ambient successive caps. -/

@[expose] public section
namespace Finsler.DoubleCapCoverComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable (X : TopCat.{0}) {ι : Type*} (W : ι → Set X) (A D : Set X)
  (hW : ∀ i, W i ⊆ A ∨ W i ⊆ D) (k p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X k)
  (hφ : cochainPullback (SupportedCap.subspaceMap X A) k φ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) p)

include hW hφ

theorem domain_good (q : ℕ) (σ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌)
    (hcap : (TopCat.toSSet.obj X).ιChainComplex σ.val ≫
      PartialDoubleCap.cap X k p q φ (TubeCochainExtension.extend X D p ψ) ≠ 0) :
    Set.range (X.toSSetObjEquiv _ σ.val) ⊆ D := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X W σ.val).mp σ.property
  rcases hW i with hA | hD
  · have hz := SupportedCap.cap_zero_on_simplex X A k (p + q) (k + (p + q)) rfl φ hφ σ.val (hi.trans hA)
    exact (hcap (by rw [PartialDoubleCap.cap, ← Category.assoc, hz, zero_comp])).elim
  · exact hi.trans hD

theorem agreement_of_domain_lift (q : ℕ)
    (c : (small X W).X (k + (p + q)) ⟶ (chains (TopCat.of D)).X q)
    (hc : c ≫ (push (SupportedCap.subspaceMap X D)).f q =
      (inclusion X W).f (k + (p + q)) ≫
        PartialDoubleCap.cap X k p q φ (TubeCochainExtension.extend X D p ψ)) :
    (SmallCoverRefinement.map X W (SupportedCap.cover X A D)
      (fun i => by rcases hW i with h | h; exact ⟨false, h⟩; exact ⟨true, h⟩)).f (k + (p + q)) ≫
      SupportedDoubleCap.localized X A D k p φ hφ ψ q (k + (p + q)) rfl = c := by
  haveI : Mono ((push (SupportedCap.subspaceMap X D)).f q) := SupportedCap.subspacePush_mono X D q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X D)).f q)).mp
  rw [Category.assoc, SupportedDoubleCap.localized_inclusion, hc]
  have hi := congrArg (fun f => f.f (k + (p + q)))
    (SmallCoverRefinement.map_inclusion X W (SupportedCap.cover X A D)
      (fun i => by rcases hW i with h | h; exact ⟨false, h⟩; exact ⟨true, h⟩))
  simpa only [HomologicalComplex.comp_f, PartialDoubleCap.cap, Category.assoc] using congrArg
    (fun t => t ≫ PartialDoubleCap.cap X k p q φ (TubeCochainExtension.extend X D p ψ)) hi

end
end Finsler.DoubleCapCoverComparison
