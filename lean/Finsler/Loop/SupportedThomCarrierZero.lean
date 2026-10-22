module

public import Finsler.Loop.MultiFarSupportedCochain
public import Finsler.Topology.SelfCutEndpoints

/-! An actual supported cut is zero on a carrier where its Thom
cochain is zero. This includes the original multi-far small approximation
and arbitrary source degree transports. No near-output support is needed. -/
@[expose] public section
namespace Finsler.SupportedThomCarrierZero
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem cut_map_zero {X Y : TopCat.{0}} (A B S : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
    (p q N : ℕ) (hN : p + q = N) (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) p θ = 0)
    (f : Y ⟶ X) (hf : ∀ y, f y ∈ S) :
    (push f).f N ≫ SupportedCap.cut X A B hA hB hc p q N hN θ hs = 0 := by
  subst N
  exact SelfCutEndpoints.cut_map_zero A B S hA hB hc p q θ hs hS f hf

variable (X : TopCat.{0}) {ι : Type*} (A : ι → Set X) (B : Set X)
  (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hc : (⋃ i, A i) ∪ B = Set.univ)
  (S : Set X) (p q N : ℕ) (hN : p + q = N) (θ : singularCochainGroup (ZMod 2) X p)
  (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p θ = 0)
  (hS : cochainPullback (SupportedCap.subspaceMap X S) p θ = 0)

include hS in
theorem multi_cut_zero_of_supported {c : coeff ⟶ (chains X).X N}
    (hcar : c ∈ supported X (fun _ : Unit => S) N) :
    c ≫ MultiFarSupportedCap.cut X A B hA hB hc p q N hN θ hs = 0 := by
  subst N
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  rw [zero_comp, Category.assoc, MultiFarSupportedCap.cut_inclusion, ← Category.assoc]
  exact SupportedCapAnnihilation.cap_zero_of_supported S p q θ hS
    (approximation_preserves (MultiFarSupportedCap.cover X A B) (fun _ : Unit => S) hcar)

include hS in
theorem multi_cut_map_zero {Y : TopCat.{0}} (f : Y ⟶ X) (hf : ∀ y, f y ∈ S) :
    (push f).f N ≫ MultiFarSupportedCap.cut X A B hA hB hc p q N hN θ hs = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  rw [← Category.assoc, push, SSet.ι_chainComplexMap_f, comp_zero]
  apply multi_cut_zero_of_supported X A B hA hB hc S p q N hN θ hs hS
  have ht : (TopCat.toSSet.map f).app (Opposite.op ⦋N⦌) σ ∈
      (X.smallSingularSubcomplex (fun _ : Unit => S)).obj (Opposite.op ⦋N⦌) := by
    apply (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => S) _).mpr
    refine ⟨(), ?_⟩
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨z, rfl⟩
    exact hf _
  exact TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) (U := fun _ : Unit => S) ⟨_, ht⟩

include hS in
theorem multi_scalar_zero (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    cochainPullback (SupportedCap.subspaceMap X S) N
      (MultiFarSupportedCap.cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0 := by
  have hz := congrArg (fun c => c ≫ ψ)
    (multi_cut_map_zero X A B hA hB hc S p q N hN θ hs hS (SupportedCap.subspaceMap X S) (fun z => z.property))
  simp only [Category.assoc, zero_comp] at hz
  exact hz

end
end Finsler.SupportedThomCarrierZero
