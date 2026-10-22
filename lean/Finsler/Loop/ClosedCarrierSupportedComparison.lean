module

public import Finsler.Loop.LocalizedSupportedCapComparison

/-! A genuine closed-carrier cap can be compared to a supported cap in
an arbitrarily smaller open near subset contained in that carrier.
The carrier itself need not be open. Common-input chain monicity and
the actual input homology section remove the restriction. -/

@[expose] public section
namespace Finsler.ClosedCarrierSupportedComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set X)
  (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
  (D : Set X) (hBD : B ⊆ D)

def nearInclusion : TopCat.of B ⟶ TopCat.of D :=
  TopCat.ofHom ⟨fun x => ⟨x.val, hBD x.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem near_source : nearInclusion X B D hBD ≫ SupportedCap.subspaceMap X D = SupportedCap.subspaceMap X B := rfl

variable (d : ℕ) (φ : singularCochainGroup (ZMod 2) X d)
  (hs : cochainPullback (SupportedCap.subspaceMap X A) d φ = 0)
  (hφ : cochainCoboundary (ZMod 2) X d φ = 0)
  (c : DegreeLoweringHomology.Map (small X U) (chains (TopCat.of D)) d)
  (hsource : ∀ q, c.component q ≫ (push (SupportedCap.subspaceMap X D)).f q =
    (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl φ)

include hsource in
theorem common_component (q : ℕ) :
    (LocalizedSupportedCapComparison.leftMap X U A B).f (d + q) ≫ c.component q =
    (inclusion X (LocalizedSupportedCapComparison.common X U A B)).f (d + q) ≫
      SupportedCap.cut X A B hA hB hc d q (d + q) rfl φ hs ≫ (push (nearInclusion X B D hBD)).f q := by
  have : Mono ((push (SupportedCap.subspaceMap X D)).f q) := SupportedCap.subspacePush_mono X D q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X D)).f q)).mp
  have hi : push (nearInclusion X B D hBD) ≫ push (SupportedCap.subspaceMap X D) = push (SupportedCap.subspaceMap X B) := by
    rw [← push_comp, near_source]
  have hfix := SmallSupportedCapRestriction.approximation_fixed
    (LocalizedSupportedCapComparison.common X U A B) (SupportedCap.cover X A B) (𝟙 X) Prod.snd
    (PullbackPairCover.maps_right U (SupportedCap.cover X A B) (𝟙 X) (𝟙 X))
  simp only [FarDiagonalCutComparison.push_identity, Category.id_comp, Category.comp_id] at hfix
  have hfixq := congrArg (fun f => f.f (d + q)) hfix
  simp only [HomologicalComplex.comp_f] at hfixq
  have hcut := SupportedCap.cut_inclusion X A B hA hB hc d q (d + q) rfl φ hs
  change SupportedCap.cut X A B hA hB hc d q (d + q) rfl φ hs ≫ (push (SupportedCap.subspaceMap X B)).f q =
    (singularSmallApprox coeff (SupportedCap.cover X A B)).f (d + q) ≫ absoluteChain X d q (d + q) rfl φ at hcut
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, hi]
  calc
    _ = ((LocalizedSupportedCapComparison.leftMap X U A B) ≫ inclusion X U).f (d + q) ≫
        absoluteChain X d q (d + q) rfl φ := by
      simpa only [HomologicalComplex.comp_f, Category.assoc] using
        congrArg (fun z => (LocalizedSupportedCapComparison.leftMap X U A B).f (d + q) ≫ z) (hsource q)
    _ = (inclusion X (LocalizedSupportedCapComparison.common X U A B)).f (d + q) ≫
        absoluteChain X d q (d + q) rfl φ := by rw [LocalizedSupportedCapComparison.left_source]
    _ = _ := by rw [hcut, ← Category.assoc, hfixq]

variable (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)

def unrefined := c.pre (smallSingularRetraction (X := X) coeff U hU hcU)

include hsource in
theorem homology_eq (q : ℕ) : (unrefined X U D d c hU hcU).homology q =
    ((SupportedCapHomology.operation X A B hA hB hc d φ hs hφ).post (push (nearInclusion X B D hBD))).homology q := by
  apply SmallInclusionHomologyCancellation.homology_eq X (LocalizedSupportedCapComparison.common X U A B)
    (LocalizedSupportedCapComparison.common_open X U A B hA hB hU)
    (LocalizedSupportedCapComparison.common_univ X U A B hc hcU) (chains (TopCat.of D)) d _ _ q
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro k
  change (inclusion X (LocalizedSupportedCapComparison.common X U A B)).f (d + k) ≫
    ((smallSingularRetraction (X := X) coeff U hU hcU).f (d + k) ≫ c.component k) = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f, LocalizedSupportedCapComparison.common_retraction]
  exact common_component X U A B hA hB hc D hBD d φ hs c hsource k

end
end Finsler.ClosedCarrierSupportedComparison
