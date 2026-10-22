module

public import Finsler.Topology.PartialDoubleCap

/-! Linear small-chain operations lifting the actual successive caps
through a partial-map domain and its bounded target. The only boundary
input is the actual successive-cap identity on the source small chains;
global closure of a zero extension is not postulated. -/

@[expose] public section
namespace Finsler.PartialDoubleCapFiltered

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (X Y : TopCat.{0}) {ι : Type*} (W : ι → Set X) (D : Set X)
  (f : TopCat.of D ⟶ Y) (B : Set Y) (k p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
  (hgood : ∀ q (σ : (X.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ PartialDoubleCap.cap X k p q φ ψ ≠ 0 →
      ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B)

def domainComponent (q : ℕ) : (small X W).X (k + (p + q)) ⟶ (chains (TopCat.of D)).X q :=
  PartialDoubleCap.localized X W D k p φ ψ
    (fun q σ hc z hz => (hgood q σ hc z hz).choose) q

theorem domain_inclusion (q : ℕ) :
    domainComponent X Y W D f B k p φ ψ hgood q ≫ (push (SupportedCap.subspaceMap X D)).f q =
      (inclusion X W).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ :=
  PartialDoubleCap.localized_inclusion X W D k p φ ψ _ q

def outputComponent (q : ℕ) : (small X W).X (k + (p + q)) ⟶ (chains (TopCat.of B)).X q :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex W : SSet).isColimitChainComplexXCofan coeff (k + (p + q)))
    fun σ => (PartialDoubleCap.exists_filtered_simplex D f B k p q φ ψ σ.val (hgood q σ)).choose_spec.choose

theorem output_inclusion (q : ℕ) :
    outputComponent X Y W D f B k p φ ψ hgood q ≫ (push (SupportedCap.subspaceMap Y B)).f q =
      domainComponent X Y W D f B k p φ ψ hgood q ≫ (push f).f q := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
  intro σ
  let h := PartialDoubleCap.exists_filtered_simplex D f B k p q φ ψ σ.val (hgood q σ)
  have he : (X.smallSingularSubcomplex W : SSet).ιChainComplex σ ≫
      outputComponent X Y W D f B k p φ ψ hgood q = h.choose_spec.choose := Cofan.IsColimit.fac _ _ σ
  have hi : ((X.smallSingularSubcomplex W : SSet).ιChainComplex σ ≫
      domainComponent X Y W D f B k p φ ψ hgood q) ≫ (push (SupportedCap.subspaceMap X D)).f q =
        (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ PartialDoubleCap.cap X k p q φ ψ := by
    rw [Category.assoc, domain_inclusion]
    simp only [← Category.assoc, inclusion, SSet.ι_chainComplexMap_f,
      Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  have hc : h.choose = (X.smallSingularSubcomplex W : SSet).ιChainComplex σ ≫
      domainComponent X Y W D f B k p φ ψ hgood q := by
    haveI : Mono ((push (SupportedCap.subspaceMap X D)).f q) := SupportedCap.subspacePush_mono X D q
    apply (cancel_mono ((push (SupportedCap.subspaceMap X D)).f q)).mp
    exact h.choose_spec.choose_spec.1.trans hi.symm
  rw [← Category.assoc, he, h.choose_spec.choose_spec.2, hc, Category.assoc]

variable
  (hcomm : ∀ q, ((inclusion X W).f (k + (p + (q + 1))) ≫ PartialDoubleCap.cap X k p (q + 1) φ ψ) ≫
    (chains X).d (q + 1) q =
      (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
        ((inclusion X W).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ))

include hcomm

theorem domain_boundary (q : ℕ) :
    domainComponent X Y W D f B k p φ ψ hgood (q + 1) ≫ (chains (TopCat.of D)).d (q + 1) q =
      (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
        domainComponent X Y W D f B k p φ ψ hgood q := by
  haveI : Mono ((push (SupportedCap.subspaceMap X D)).f q) := SupportedCap.subspacePush_mono X D q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X D)).f q)).mp
  rw [Category.assoc, ← (push (SupportedCap.subspaceMap X D)).comm, ← Category.assoc,
    domain_inclusion]
  simp only [Category.assoc]
  rw [domain_inclusion]
  simpa only [Category.assoc] using hcomm q

theorem output_boundary (q : ℕ) :
    outputComponent X Y W D f B k p φ ψ hgood (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
        outputComponent X Y W D f B k p φ ψ hgood q := by
  haveI : Mono ((push (SupportedCap.subspaceMap Y B)).f q) := SupportedCap.subspacePush_mono Y B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap Y B)).f q)).mp
  rw [Category.assoc, ← (push (SupportedCap.subspaceMap Y B)).comm, ← Category.assoc,
    output_inclusion, Category.assoc, (push f).comm, ← Category.assoc,
    domain_boundary X Y W D f B k p φ ψ hgood hcomm q]
  simp only [Category.assoc]
  rw [output_inclusion]

end
end Finsler.PartialDoubleCapFiltered
