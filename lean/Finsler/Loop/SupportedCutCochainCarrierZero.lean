module

public import Finsler.Topology.TubeExtensionPullback
public import Finsler.Topology.CarrierCochainZero
public import Finsler.Topology.SmallCapCarrier

/-! The ORIGINAL supported cut followed by a neighborhood cochain
vanishes on a carrier C whenever that cochain is zero on B intersect C.
Extend by zero on the actual simplex basis, then use the already
verified image preservation of the ORIGINAL small approximation and
Alexander-Whitney cap. No homology or closure premise is needed. -/
@[expose] public section
namespace Finsler.SupportedCutCochainCarrierZero
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : TopCat.{0}) (A B C : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hcover : A ∪ B = Set.univ) (p q : ℕ)
  (φ : singularCochainGroup (ZMod 2) X p)
  (hφ : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
  (hψ : cochainPullback (restriction (SupportedCap.subspaceMap X C)
    ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0)

include hψ in
theorem zero_of_supported {c : coeff ⟶ (chains X).X (p + q)}
    (hc : c ∈ supported X (fun _ : Unit => C) (p + q)) :
    c ≫ SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hφ ≫ ψ = 0 := by
  let Ψ := TubeCochainExtension.extend X B q ψ
  have hzero : cochainPullback (SupportedCap.subspaceMap X C) q Ψ = 0 :=
    TubeExtensionPullback.pullback_zero (SupportedCap.subspaceMap X C) B q ψ hψ
  have happrox := approximation_preserves (SupportedCap.cover X A B) (fun _ : Unit => C) hc
  have hcap := SmallCapCarrier.cap_preserves (fun _ : Unit => C) p q (p + q) rfl φ happrox
  have hz := CarrierCochainZero.carried_zero (fun _ : Unit => C) q Ψ (fun _ => hzero) hcap
  have he : ψ = (push (SupportedCap.subspaceMap X B)).f q ≫ Ψ :=
    (TubeCochainExtension.restriction X B q ψ).symm
  have hcut := SupportedCap.cut_inclusion X A B hA hB hcover p q (p + q) rfl φ hφ
  change SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hφ ≫
    (push (SupportedCap.subspaceMap X B)).f q =
    (TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)).f (p + q) ≫
      absoluteChain X p q (p + q) rfl φ at hcut
  calc
    _ = c ≫ SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hφ ≫
        ((push (SupportedCap.subspaceMap X B)).f q ≫ Ψ) := congrArg
          (fun a => c ≫ SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hφ ≫ a) he
    _ = c ≫ (SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hφ ≫
        (push (SupportedCap.subspaceMap X B)).f q) ≫ Ψ := by simp only [Category.assoc]
    _ = c ≫ ((TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)).f (p + q) ≫
        absoluteChain X p q (p + q) rfl φ) ≫ Ψ := by rw [hcut]
    _ = 0 := by simpa only [Category.assoc] using hz

include hψ in
theorem subspace_cochain_zero :
    (push (SupportedCap.subspaceMap X C)).f (p + q) ≫
      SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hφ ≫ ψ = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of C)) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj (TopCat.of C)).ιChainComplex σ ≫
    ((push (SupportedCap.subspaceMap X C)).f (p + q) ≫
      SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hφ ≫ ψ) = 0
  rw [← Category.assoc, ← Category.assoc, push, SSet.ι_chainComplexMap_f]
  let τ := (TopCat.toSSet.map (SupportedCap.subspaceMap X C)).app _ σ
  have ht : τ ∈ (X.smallSingularSubcomplex (fun _ : Unit => C)).obj (Opposite.op ⦋p + q⦌) := by
    apply (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => C) τ).mpr
    exact ⟨(), TubeCochainExtension.included_range X C σ⟩
  exact zero_of_supported X A B C hA hB hcover p q φ hφ ψ hψ
    (TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) ⟨τ, ht⟩)

end
end Finsler.SupportedCutCochainCarrierZero
