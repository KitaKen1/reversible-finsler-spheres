module

public import Finsler.Topology.SupportedCap
public import Finsler.Topology.SupportedCapNaturality
public import Finsler.Topology.RelativeCapBoundary
public import TauCeti.AlgebraicTopology.Singular.Subspace

/-! Literal annihilation by the supported Thom cut. Vanishing of the
cochain on a subspace kills all chains carried by that subspace even after
the actual image-preserving small-chain approximation. -/

@[expose] public section
namespace Finsler.SupportedCapAnnihilation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Set
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem small_cap_zero (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0) :
    (inclusion X (fun _ : Unit => A)).f (p + q) ≫ absoluteChain X p q (p + q) rfl φ = 0 := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex (fun _ : Unit => A) : SSet))
    (R := coeff)
  intro σ
  obtain ⟨_, hσ⟩ := (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => A) σ.val).mp σ.property
  have hr := (TopCat.mem_range_toSSet_subtypeVal_iff A (Opposite.op ⦋p + q⦌) σ.val).mpr hσ
  change σ.val ∈ Set.range ((TopCat.toSSet.map (SupportedCap.subspaceMap X A)).app
    (Opposite.op ⦋p + q⦌)) at hr
  obtain ⟨τ, hτ⟩ := hr
  have he : (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
      (SupportedCapNaturality.push (SupportedCap.subspaceMap X A)).f (p + q) =
        (TopCat.toSSet.obj X).ιChainComplex σ.val := by
    have h := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of A))
      (Y := TopCat.toSSet.obj X) (f := TopCat.toSSet.map (SupportedCap.subspaceMap X A))
      (R := coeff) τ
    exact h.trans (congrArg (fun t => (TopCat.toSSet.obj X).ιChainComplex (R := coeff) t) hτ)
  calc
    _ = (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X p q (p + q) rfl φ := by
      rw [← Category.assoc, SSet.ι_chainComplexMap_f]
      simp only [Subfunctor.ι_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
    _ = ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        (SupportedCapNaturality.push (SupportedCap.subspaceMap X A)).f (p + q)) ≫
          absoluteChain X p q (p + q) rfl φ := by rw [he]
    _ = (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        (absoluteChain (TopCat.of A) p q (p + q) rfl
          (cochainPullback (SupportedCap.subspaceMap X A) p φ) ≫
            (SupportedCapNaturality.push (SupportedCap.subspaceMap X A)).f q) := by
      simpa only [SupportedCapNaturality.push, Category.assoc] using
        congrArg (fun m => (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫ m)
          (RelativeCapBoundary.absolute_chain_natural (SupportedCap.subspaceMap X A)
            p q (p + q) rfl φ).symm
    _ = _ := by simp only [hφ, map_zero, zero_comp, comp_zero]

theorem cap_zero_of_supported {X : TopCat.{0}} (A : Set X) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    {f : coeff ⟶ (chains X).X (p + q)} (hf : f ∈ supported X (fun _ : Unit => A) (p + q)) :
    f ≫ absoluteChain X p q (p + q) rfl φ = 0 := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hf
  rw [Category.assoc, small_cap_zero X A p q φ hφ, comp_zero]

theorem cut_zero_of_supported (X : TopCat.{0}) (A B C : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hAφ : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hCφ : cochainPullback (SupportedCap.subspaceMap X C) p φ = 0)
    {f : coeff ⟶ (chains X).X (p + q)} (hf : f ∈ supported X (fun _ : Unit => C) (p + q)) :
    f ≫ SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hAφ = 0 := by
  let j := SupportedCapNaturality.push (SupportedCap.subspaceMap X B)
  haveI : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  rw [zero_comp]
  have he : SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hAφ ≫ j.f q =
      (TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)).f (p + q) ≫
        absoluteChain X p q (p + q) rfl φ :=
    SupportedCap.cut_inclusion X A B hA hB hcover p q (p + q) rfl φ hAφ
  calc
    _ = f ≫ (SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hAφ ≫ j.f q) :=
      Category.assoc _ _ _
    _ = f ≫ ((TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)).f (p + q) ≫
        absoluteChain X p q (p + q) rfl φ) := congrArg (fun m => f ≫ m) he
    _ = (f ≫ (TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)).f (p + q)) ≫
        absoluteChain X p q (p + q) rfl φ := (Category.assoc _ _ _).symm
    _ = 0 := cap_zero_of_supported C p q φ hCφ
      (approximation_preserves (SupportedCap.cover X A B) (fun _ : Unit => C) hf)

end
end Finsler.SupportedCapAnnihilation
