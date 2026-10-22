module

public import Finsler.Topology.PartialDoubleCap

/-! Successive caps on a far/domain refinement depend only on the
restriction of the second cochain to the genuine domain. Neither
ambient second cochain is assumed closed or equal outside the domain. -/

@[expose] public section
namespace Finsler.LocalizedDoubleCapAgreement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem on_cover (X : TopCat.{0}) {ι : Type*} (U : ι → Set X) (A D : Set X)
    (hU : ∀ i, U i ⊆ A ∨ U i ⊆ D) (k p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) k φ = 0)
    (ψ₀ ψ₁ : singularCochainGroup (ZMod 2) X p)
    (hψ : cochainPullback (SupportedCap.subspaceMap X D) p ψ₀ =
      cochainPullback (SupportedCap.subspaceMap X D) p ψ₁) (q : ℕ) :
    (inclusion X U).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ₀ =
      (inclusion X U).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ₁ := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex U : SSet)) (R := coeff)
  intro σ
  simp only [inclusion, SSet.ι_chainComplexMap_f_assoc,
    Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  change (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ PartialDoubleCap.cap X k p q φ ψ₀ =
    (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ PartialDoubleCap.cap X k p q φ ψ₁
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X U σ.val).mp σ.property
  rcases hU i with hA | hD
  · have hz := SupportedCap.cap_zero_on_simplex X A k (p + q) (k + (p + q)) rfl φ hφ σ.val
      (hi.trans hA)
    simp only [PartialDoubleCap.cap, ← Category.assoc, hz, zero_comp]
  · have h₀ := PartialDoubleCap.lifted_simplex_inclusion X D k p q φ ψ₀ σ.val (hi.trans hD)
    have h₁ := PartialDoubleCap.lifted_simplex_inclusion X D k p q φ ψ₁ σ.val (hi.trans hD)
    rw [hψ] at h₀
    exact h₀.symm.trans h₁

end
end Finsler.LocalizedDoubleCapAgreement
