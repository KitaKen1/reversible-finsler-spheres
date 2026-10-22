module

public import Finsler.Loop.SupportedCutCochainCarrierZero
public import Finsler.Topology.RelativeCapDual

/-! Exact near restriction and far annihilation of the ORIGINAL cut.
This identifies both sequential caps on a genuine common near set;
the actual small approximation is fixed there, not assumed natural. -/
@[expose] public section
namespace Finsler.SupportedCapNearRestriction
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) (A B : Set X)

def nearLift : TopCat.toSSet.obj (TopCat.of B) ⟶
    (X.smallSingularSubcomplex (SupportedCap.cover X A B) : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (SupportedCap.subspaceMap X B)) (by
    rintro N _ ⟨σ, rfl⟩
    apply (TopCat.mem_smallSingularSubcomplex_iff X (SupportedCap.cover X A B) _).mpr
    exact ⟨true, TubeCochainExtension.included_range X B σ⟩)

theorem nearLift_inclusion : nearLift X A B ≫
    (X.smallSingularSubcomplex (SupportedCap.cover X A B)).ι =
    TopCat.toSSet.map (SupportedCap.subspaceMap X B) := SSet.Subcomplex.lift_ι _ _

theorem approximation_near_fixed : push (SupportedCap.subspaceMap X B) ≫
    TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B) =
    push (SupportedCap.subspaceMap X B) := by
  have he : SSet.chainComplexMap (nearLift X A B) coeff ≫
      inclusion X (SupportedCap.cover X A B) = push (SupportedCap.subspaceMap X B) := by
    rw [inclusion, ← Functor.map_comp, nearLift_inclusion]
    rfl
  rw [← he, Category.assoc, TauCeti.ι_comp_singularSmallApprox]

variable (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
  (p q N : ℕ) (hN : p + q = N) (θ : singularCochainGroup (ZMod 2) X p)
  (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)

theorem cut_near :
    (push (SupportedCap.subspaceMap X B)).f N ≫ SupportedCap.cut X A B hA hB hc p q N hN θ hs =
      absoluteChain (TopCat.of B) p q N hN (cochainPullback (SupportedCap.subspaceMap X B) p θ) := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  have hf := congrArg (fun f => f.f N) (approximation_near_fixed X A B)
  simp only [HomologicalComplex.comp_f] at hf
  have hi := SupportedCap.cut_inclusion X A B hA hB hc p q N hN θ hs
  have hn := RelativeCapBoundary.absolute_chain_natural (SupportedCap.subspaceMap X B) p q N hN θ
  calc
    _ = j.f N ≫ ((TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)).f N ≫
        absoluteChain X p q N hN θ) := by
      simpa only [j, push, Category.assoc] using congrArg (fun f => j.f N ≫ f) hi
    _ = j.f N ≫ absoluteChain X p q N hN θ := by
      rw [← Category.assoc, hf]
    _ = _ := by simpa only [j, push] using hn.symm

theorem cut_far :
    (push (SupportedCap.subspaceMap X A)).f N ≫ SupportedCap.cut X A B hA hB hc p q N hN θ hs = 0 := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  rw [zero_comp, Category.assoc]
  have hi := SupportedCap.cut_inclusion X A B hA hB hc p q N hN θ hs
  change SupportedCap.cut X A B hA hB hc p q N hN θ hs ≫ j.f q = _ at hi
  rw [hi]
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of A)) (R := coeff)
  intro σ
  simp only [← Category.assoc, push, SSet.ι_chainComplexMap_f, comp_zero]
  let τ := (TopCat.toSSet.map (SupportedCap.subspaceMap X A)).app _ σ
  have ht : τ ∈ (X.smallSingularSubcomplex (fun _ : Unit => A)).obj (Opposite.op ⦋N⦌) :=
    (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => A) τ).mpr
      ⟨(), TubeCochainExtension.included_range X A σ⟩
  have hp := approximation_preserves (SupportedCap.cover X A B) (fun _ : Unit => A)
    (TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) ⟨τ, ht⟩)
  simpa only [τ, Category.assoc] using
    CarrierCochainZero.cap_zero (fun _ : Unit => A) p q N hN θ (fun _ => hs) hp

theorem cut_near_map {Y : TopCat.{0}} (g : Y ⟶ TopCat.of B) :
    (push (g ≫ SupportedCap.subspaceMap X B)).f N ≫ SupportedCap.cut X A B hA hB hc p q N hN θ hs =
      absoluteChain Y p q N hN (cochainPullback (g ≫ SupportedCap.subspaceMap X B) p θ) ≫ (push g).f q := by
  rw [push_comp, HomologicalComplex.comp_f, Category.assoc, cut_near, pullback_comp]
  simpa only [push] using
    (RelativeCapBoundary.absolute_chain_natural g p q N hN
      (cochainPullback (SupportedCap.subspaceMap X B) p θ)).symm

theorem cut_far_map {Y : TopCat.{0}} (g : Y ⟶ TopCat.of A) :
    (push (g ≫ SupportedCap.subspaceMap X A)).f N ≫ SupportedCap.cut X A B hA hB hc p q N hN θ hs = 0 := by
  rw [push_comp, HomologicalComplex.comp_f, Category.assoc, cut_far, comp_zero]

end
end Finsler.SupportedCapNearRestriction
