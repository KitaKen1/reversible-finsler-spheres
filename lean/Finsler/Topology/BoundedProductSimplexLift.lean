module

public import Finsler.Topology.ProductSimplexCarrier
public import Finsler.Topology.PartialDoubleCapDomainFiltered

/-! Lift the genuine universal product of singular simplices into the
existing bounded partial-map domain, retaining its parameters and both
literal source and output inclusions. A whole-rectangle bound supplies
all faces and degeneracies at once. -/

@[expose] public section
namespace Finsler.BoundedProductSimplexLift

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (P Q R : TopCat.{0}) {j k : ℕ}
  (σ : TopCat.toSSet.obj P _⦋j⦌) (τ : TopCat.toSSet.obj Q _⦋k⦌)
  (D : Set (P ⊗ Q : TopCat.{0})) (f : TopCat.of D ⟶ R) (B : Set R)
  (hgood : ∀ z ∈ ProductSimplexCarrier.rectangle P Q σ τ, ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B)

def domain : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj (TopCat.of D) :=
  ProductSimplexCarrier.lift P Q σ τ D (fun z hz => (hgood z hz).choose)

theorem domain_bounded (n : ℕ) (z : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) _⦋n⦌) :
    Set.range ((TopCat.of D).toSSetObjEquiv _ ((domain P Q R σ τ D f B hgood).app _ z)) ⊆
      PartialDoubleCapDomainFiltered.boundedDomain (P ⊗ Q) R D f B := by
  intro x hx
  have hp : x.val ∈ ProductSimplexCarrier.rectangle P Q σ τ := by
    apply ProductSimplexCarrier.model_parent P Q σ τ n z
    exact PartialDoubleCap.lifted_parent (P ⊗ Q) D
      ((ProductSimplexCarrier.model P Q σ τ).app _ z)
      ((ProductSimplexCarrier.model_parent P Q σ τ n z).trans (fun w hw => (hgood w hw).choose)) x hx
  exact (hgood x.val hp).choose_spec

def toBounded : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj
    (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain (P ⊗ Q) R D f B)) :=
  SimplicialCarrierLift.lift (TopCat.of D)
    (PartialDoubleCapDomainFiltered.boundedDomain (P ⊗ Q) R D f B)
    (domain P Q R σ τ D f B hgood) (domain_bounded P Q R σ τ D f B hgood)

theorem source_inclusion :
    toBounded P Q R σ τ D f B hgood ≫
      TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of D)
        (PartialDoubleCapDomainFiltered.boundedDomain (P ⊗ Q) R D f B)) ≫
      TopCat.toSSet.map (SupportedCap.subspaceMap (P ⊗ Q) D) =
        ProductSimplexCarrier.model P Q σ τ := by
  unfold toBounded
  rw [← Category.assoc, SimplicialCarrierLift.lift_inclusion]
  exact ProductSimplexCarrier.lift_inclusion P Q σ τ D (fun z hz => (hgood z hz).choose)

theorem retained_inclusion :
    toBounded P Q R σ τ D f B hgood ≫
      TopCat.toSSet.map (PartialDoubleCapDomainFiltered.retained (P ⊗ Q) R D f B) ≫
      TopCat.toSSet.map (SupportedCap.subspaceMap R B) =
        domain P Q R σ τ D f B hgood ≫ TopCat.toSSet.map f := by
  have he : PartialDoubleCapDomainFiltered.retained (P ⊗ Q) R D f B ≫
      SupportedCap.subspaceMap R B =
      SupportedCap.subspaceMap (TopCat.of D)
        (PartialDoubleCapDomainFiltered.boundedDomain (P ⊗ Q) R D f B) ≫ f := by
    ext z : 1
    rfl
  rw [← Functor.map_comp, he, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun G => G ≫ TopCat.toSSet.map f)
    (SimplicialCarrierLift.lift_inclusion (TopCat.of D)
      (PartialDoubleCapDomainFiltered.boundedDomain (P ⊗ Q) R D f B)
      (domain P Q R σ τ D f B hgood) (domain_bounded P Q R σ τ D f B hgood))

end
end Finsler.BoundedProductSimplexLift
