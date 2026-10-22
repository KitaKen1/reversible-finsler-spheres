module

public import Finsler.Loop.MultiFarSupportedCochain
public import Finsler.Loop.SupportedCapNearRestriction

/-! Exact near restriction and separate far annihilation for the genuine
multi-far cap. These are actual chain identities, retaining its chosen
small approximation; the far union is never used as a support claim. -/
@[expose] public section
namespace Finsler.MultiFarCapRestriction
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.MultiFarSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) {ι : Type*} (A : ι → Set X) (B : Set X)

def nearLift : TopCat.toSSet.obj (TopCat.of B) ⟶
    (X.smallSingularSubcomplex (cover X A B) : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (SupportedCap.subspaceMap X B)) (by
    rintro N _ ⟨σ, rfl⟩
    apply (TopCat.mem_smallSingularSubcomplex_iff X (cover X A B) _).mpr
    exact ⟨none, TubeCochainExtension.included_range X B σ⟩)

theorem nearLift_inclusion : nearLift X A B ≫ (X.smallSingularSubcomplex (cover X A B)).ι =
    TopCat.toSSet.map (SupportedCap.subspaceMap X B) := SSet.Subcomplex.lift_ι _ _

theorem approximation_near_fixed : push (SupportedCap.subspaceMap X B) ≫
    TauCeti.singularSmallApprox coeff (cover X A B) = push (SupportedCap.subspaceMap X B) := by
  have he : SSet.chainComplexMap (nearLift X A B) coeff ≫ inclusion X (cover X A B) =
      push (SupportedCap.subspaceMap X B) := by
    rw [inclusion, ← Functor.map_comp, nearLift_inclusion]
    rfl
  rw [← he, Category.assoc, TauCeti.ι_comp_singularSmallApprox]

variable (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hc : (⋃ i, A i) ∪ B = Set.univ)
  (p q N : ℕ) (hN : p + q = N) (θ : singularCochainGroup (ZMod 2) X p)
  (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p θ = 0)

theorem cut_near : (push (SupportedCap.subspaceMap X B)).f N ≫ cut X A B hA hB hc p q N hN θ hs =
    absoluteChain (TopCat.of B) p q N hN (cochainPullback (SupportedCap.subspaceMap X B) p θ) := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  have hf := congrArg (fun f => f.f N) (approximation_near_fixed X A B)
  simp only [HomologicalComplex.comp_f] at hf
  have hi := cut_inclusion X A B hA hB hc p q N hN θ hs
  have hn := RelativeCapBoundary.absolute_chain_natural (SupportedCap.subspaceMap X B) p q N hN θ
  calc
    _ = j.f N ≫ ((TauCeti.singularSmallApprox coeff (cover X A B)).f N ≫ absoluteChain X p q N hN θ) := by
      simpa only [j, push, Category.assoc] using congrArg (fun f => j.f N ≫ f) hi
    _ = j.f N ≫ absoluteChain X p q N hN θ := by rw [← Category.assoc, hf]
    _ = _ := by simpa only [j, push] using hn.symm

theorem cut_far (i : ι) :
    (push (SupportedCap.subspaceMap X (A i))).f N ≫ cut X A B hA hB hc p q N hN θ hs = 0 := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  rw [zero_comp, Category.assoc]
  have hi := cut_inclusion X A B hA hB hc p q N hN θ hs
  change cut X A B hA hB hc p q N hN θ hs ≫ j.f q = _ at hi
  rw [hi]
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of (A i))) (R := coeff)
  intro σ
  simp only [← Category.assoc, push, SSet.ι_chainComplexMap_f, comp_zero]
  let τ := (TopCat.toSSet.map (SupportedCap.subspaceMap X (A i))).app _ σ
  have ht : τ ∈ (X.smallSingularSubcomplex (fun _ : Unit => A i)).obj (Opposite.op ⦋N⦌) :=
    (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => A i) τ).mpr
      ⟨(), TubeCochainExtension.included_range X (A i) σ⟩
  have hp := approximation_preserves (cover X A B) (fun _ : Unit => A i)
    (TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) ⟨τ, ht⟩)
  simpa only [τ, Category.assoc] using
    CarrierCochainZero.cap_zero (fun _ : Unit => A i) p q N hN θ (fun _ => hs i) hp

end
end Finsler.MultiFarCapRestriction
