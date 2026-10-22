module

public import Finsler.Topology.PartialDoubleCapFiltered

/-! The actual successive caps lift through the retained-length subset of
their cut domain. This retains the cut parameter needed by a subsequent
length-preserving deformation. All comparisons are literal chain identities;
monicity is used only for subspace inclusions of singular chains. -/

@[expose] public section
namespace Finsler.PartialDoubleCapDomainFiltered

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable (X Y : TopCat.{0}) {ι : Type*} (W : ι → Set X) (D : Set X)
  (f : TopCat.of D ⟶ Y) (B : Set Y) (k p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ PartialDoubleCap.cap X k p q φ ψ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B)

def boundedDomain : Set (TopCat.of D) := f ⁻¹' B

def component (q : ℕ) : (small X W).X (k + (p + q)) ⟶
    (chains (TopCat.of (boundedDomain X Y D f B))).X q :=
  PartialDoubleCapFiltered.outputComponent X (TopCat.of D) W D (𝟙 (TopCat.of D))
    (boundedDomain X Y D f B) k p φ ψ hgood q

theorem domain_component (q : ℕ) :
    component X Y W D f B k p φ ψ hgood q ≫
      (push (SupportedCap.subspaceMap (TopCat.of D) (boundedDomain X Y D f B))).f q =
        PartialDoubleCapFiltered.domainComponent X Y W D f B k p φ ψ hgood q := by
  have he := PartialDoubleCapFiltered.output_inclusion X (TopCat.of D) W D
    (𝟙 (TopCat.of D)) (boundedDomain X Y D f B) k p φ ψ hgood q
  have hid : push (𝟙 (TopCat.of D)) = 𝟙 (chains (TopCat.of D)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (TopCat.of D))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simpa only [component, hid, PartialDoubleCapFiltered.domainComponent,
    HomologicalComplex.id_f,
    Category.comp_id] using he

theorem source_inclusion (q : ℕ) :
    component X Y W D f B k p φ ψ hgood q ≫
      (push (SupportedCap.subspaceMap (TopCat.of D) (boundedDomain X Y D f B))).f q ≫
        (push (SupportedCap.subspaceMap X D)).f q =
          (inclusion X W).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ := by
  rw [← Category.assoc, domain_component,
    PartialDoubleCapFiltered.domain_inclusion]

def retained : TopCat.of (boundedDomain X Y D f B) ⟶ TopCat.of B :=
  restriction f (boundedDomain X Y D f B) B (fun _ hz => hz)

theorem output_component (q : ℕ) :
    component X Y W D f B k p φ ψ hgood q ≫
      (push (retained X Y D f B)).f q =
        PartialDoubleCapFiltered.outputComponent X Y W D f B k p φ ψ hgood q := by
  haveI : Mono ((push (SupportedCap.subspaceMap Y B)).f q) :=
    SupportedCap.subspacePush_mono Y B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap Y B)).f q)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, retained, restriction_push,
    HomologicalComplex.comp_f, ← Category.assoc, domain_component,
    PartialDoubleCapFiltered.output_inclusion]

variable
  (hcomm : ∀ q, ((inclusion X W).f (k + (p + (q + 1))) ≫ PartialDoubleCap.cap X k p (q + 1) φ ψ) ≫
    (chains X).d (q + 1) q =
      (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
        ((inclusion X W).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ))

include hcomm

theorem component_boundary (q : ℕ) :
    component X Y W D f B k p φ ψ hgood (q + 1) ≫
      (chains (TopCat.of (boundedDomain X Y D f B))).d (q + 1) q =
        (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
          component X Y W D f B k p φ ψ hgood q :=
  PartialDoubleCapFiltered.output_boundary X (TopCat.of D) W D (𝟙 (TopCat.of D))
    (boundedDomain X Y D f B) k p φ ψ hgood hcomm q

end
end Finsler.PartialDoubleCapDomainFiltered
