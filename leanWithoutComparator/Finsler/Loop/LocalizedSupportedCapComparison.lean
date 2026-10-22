module

public import Finsler.Loop.SmallSupportedCapRestriction
public import Finsler.Loop.FarDiagonalCutComparison
public import Finsler.Topology.PullbackPairCover
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! Any genuine closed localized cap with the exact cap source diagram
agrees with the supported cap in its actual target neighborhood. A real
pairwise common cover fixes the supported approximation, and only chain
monicity and the input homology section are used. -/

@[expose] public section
namespace Finsler.LocalizedSupportedCapComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set X)
  (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)

def common := PullbackPairCover.cover U (SupportedCap.cover X A B) (𝟙 X) (𝟙 X)

def leftMap := PullbackPairCover.leftMap U (SupportedCap.cover X A B) (𝟙 X) (𝟙 X)

include hA hB in
theorem common_open (hU : ∀ i, IsOpen (U i)) (i : ι × Bool) : IsOpen (common X U A B i) :=
  PullbackPairCover.isOpen U (SupportedCap.cover X A B) (𝟙 X) (𝟙 X) hU (SupportedCap.cover_open X A B hA hB) i

include hc in
theorem common_univ (hU : ⋃ i, U i = Set.univ) : ⋃ i, common X U A B i = Set.univ :=
  PullbackPairCover.covers U (SupportedCap.cover X A B) (𝟙 X) (𝟙 X) hU (SupportedCap.cover_univ X A B hc)

theorem left_source : leftMap X U A B ≫ inclusion X U = inclusion X (common X U A B) := by
  rw [leftMap, PullbackPairCover.leftMap_inclusion, FarDiagonalCutComparison.push_identity, Category.comp_id]
  rfl

variable (d : ℕ) (φ : singularCochainGroup (ZMod 2) X d)
  (hs : cochainPullback (SupportedCap.subspaceMap X A) d φ = 0)
  (hφ : cochainCoboundary (ZMod 2) X d φ = 0)
  (c : DegreeLoweringHomology.Map (small X U) (chains (TopCat.of B)) d)
  (hsource : ∀ q, c.component q ≫ (push (SupportedCap.subspaceMap X B)).f q =
    (inclusion X U).f (d + q) ≫ absoluteChain X d q (d + q) rfl φ)

include hsource in
theorem common_component (q : ℕ) :
    (leftMap X U A B).f (d + q) ≫ c.component q =
      (inclusion X (common X U A B)).f (d + q) ≫ SupportedCap.cut X A B hA hB hc d q (d + q) rfl φ hs := by
  have : Mono ((push (SupportedCap.subspaceMap X B)).f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X B)).f q)).mp
  have hfix := SmallSupportedCapRestriction.approximation_fixed (common X U A B) (SupportedCap.cover X A B)
    (𝟙 X) Prod.snd (PullbackPairCover.maps_right U (SupportedCap.cover X A B) (𝟙 X) (𝟙 X))
  simp only [FarDiagonalCutComparison.push_identity, Category.id_comp, Category.comp_id] at hfix
  have hfixq := congrArg (fun f => f.f (d + q)) hfix
  simp only [HomologicalComplex.comp_f] at hfixq
  rw [Category.assoc, hsource q, ← Category.assoc, ← HomologicalComplex.comp_f, left_source]
  have hcut := SupportedCap.cut_inclusion X A B hA hB hc d q (d + q) rfl φ hs
  change SupportedCap.cut X A B hA hB hc d q (d + q) rfl φ hs ≫
      (push (SupportedCap.subspaceMap X B)).f q =
    (TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)).f (d + q) ≫
      absoluteChain X d q (d + q) rfl φ at hcut
  rw [Category.assoc, hcut, ← Category.assoc, hfixq]

variable (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)

def unrefined := c.pre (smallSingularRetraction (X := X) coeff U hU hcU)

theorem common_retraction : inclusion X (common X U A B) ≫ smallSingularRetraction (X := X) coeff U hU hcU =
    leftMap X U A B := by
  rw [← left_source X U A B, Category.assoc, ι_comp_smallSingularRetraction, Category.comp_id]

include hsource hφ in
theorem homology_eq (q : ℕ) : (unrefined X U B d c hU hcU).homology q =
    (SupportedCapHomology.operation X A B hA hB hc d φ hs hφ).homology q := by
  apply SmallInclusionHomologyCancellation.homology_eq X (common X U A B)
    (common_open X U A B hA hB hU) (common_univ X U A B hc hcU) (chains (TopCat.of B)) d _ _ q
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro k
  change (inclusion X (common X U A B)).f (d + k) ≫
      ((smallSingularRetraction (X := X) coeff U hU hcU).f (d + k) ≫ c.component k) = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f, common_retraction]
  exact common_component X U A B hA hB hc d φ hs c hsource k

end
end Finsler.LocalizedSupportedCapComparison
