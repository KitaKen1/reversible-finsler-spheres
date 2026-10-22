module

public import Finsler.Topology.DoubleCapEmbeddingPullback

/-! Before retaining a loop, the actual cap on the parameter-embedding
pullback is the original cut-domain cap. This identifies the domain
parameters needed by a subsequent deformation, not merely ambient
homology images. -/

@[expose] public section
namespace Finsler.DoubleCapEmbeddingFactor

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

theorem domain_factor {Z X Y : TopCat.{0}} {ι : Type*}
    (h : Z ⟶ X) (W : ι → Set X) (D : Set X) (f : TopCat.of D ⟶ Y) (B : Set Y)
    (k p : ℕ) (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (hmono : ∀ q, Mono ((push h).f q))
    (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
      (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ PartialDoubleCap.cap X k p q φ ψ ≠ 0 →
        ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B) (q : ℕ) :
    PartialDoubleCapDomainFiltered.component Z Y (DoubleCapEmbeddingPullback.cover h W)
      (h ⁻¹' D) (DoubleCapEmbeddingPullback.retained h D f) B k p
      (cochainPullback h k φ) (cochainPullback h p ψ)
      (DoubleCapEmbeddingPullback.good h W D f B k p φ ψ hmono hgood) q ≫
        (push (SupportedCap.subspaceMap (TopCat.of (h ⁻¹' D))
          (PartialDoubleCapDomainFiltered.boundedDomain Z Y (h ⁻¹' D)
            (DoubleCapEmbeddingPullback.retained h D f) B))).f q ≫
        (push (DoubleCapEmbeddingPullback.domainMap h D)).f q =
      (SmallRetractionComparison.map (X := Z) (Y := X) (DoubleCapEmbeddingPullback.cover h W)
        W h id (fun _ _ hz => hz)).f (k + (p + q)) ≫
          PartialDoubleCapFiltered.domainComponent X Y W D f B k p φ ψ hgood q := by
  let U := DoubleCapEmbeddingPullback.cover h W
  let M := SmallRetractionComparison.map (X := Z) (Y := X) U W h id (fun _ _ hz => hz)
  haveI : Mono ((push (SupportedCap.subspaceMap X D)).f q) :=
    SupportedCap.subspacePush_mono X D q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X D)).f q)).mp
  have hi := congrArg (fun g => g.f (k + (p + q)))
    (SmallRetractionComparison.map_inclusion (X := Z) (Y := X) U W h id (fun _ _ hz => hz))
  change M.f (k + (p + q)) ≫ (inclusion X W).f (k + (p + q)) =
    (inclusion Z U).f (k + (p + q)) ≫ (push h).f (k + (p + q)) at hi
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, DoubleCapEmbeddingPullback.domainMap, restriction_push,
    HomologicalComplex.comp_f]
  rw [← Category.assoc, ← Category.assoc,
    PartialDoubleCapDomainFiltered.domain_component,
    PartialDoubleCapFiltered.domain_inclusion, Category.assoc,
    PartialDoubleCap.cap_natural, ← Category.assoc, ← hi]
  rw [Category.assoc, PartialDoubleCapFiltered.domain_inclusion]

end
end Finsler.DoubleCapEmbeddingFactor
