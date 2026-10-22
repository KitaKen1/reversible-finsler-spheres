module

public import Finsler.Loop.SupportedThomTime
public import Finsler.Loop.SingleCapTimeRetraction
import all Finsler.Loop.SingleCapTimeRetraction

/-! Change only the far part of a real supported-cap cover while keeping
the near target fixed. The actual localized caps agree on the refining
small input; the genuine relative time retraction comparison removes it. -/

@[expose] public section
namespace Finsler.SupportedThomTimeRefinement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable (X : TopCat.{0}) (A B : Set X)

def localized (p : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    DegreeLoweringHomology.Map (small X (SupportedCap.cover X A B)) (chains (TopCat.of B)) p where
  component q := SupportedCap.localizedCap X A B p q (p + q) rfl φ hs
  comm q := by
    convert SupportedCap.localizedCap_boundary X A B p q (p + q) rfl φ hs hφ using 1

theorem source (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (localized X A B p φ hs hφ).component q ≫ (push (SupportedCap.subspaceMap X B)).f q =
      (inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
        RelativeCapAssociativity.absoluteChain X p q (p + q) rfl φ :=
  SupportedCap.localizedCap_inclusion X A B p q (p + q) rfl φ hs

variable (A' : Set X) (hAA : A' ⊆ A)

include hAA in
theorem cover_refines (i : Bool) : SupportedCap.cover X A' B i ⊆ SupportedCap.cover X A B i := by
  cases i
  · exact hAA
  · exact Set.Subset.rfl

include hAA in
theorem component (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hs' : cochainPullback (SupportedCap.subspaceMap X A') p φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (SmallRefinementComparison.refinement (SupportedCap.cover X A' B) (SupportedCap.cover X A B) id
      (cover_refines X A B A' hAA)).f (p + q) ≫ (localized X A B p φ hs hφ).component q =
      (localized X A' B p φ hs' hφ).component q := by
  have : Mono ((push (SupportedCap.subspaceMap X B)).f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X B)).f q)).mp
  rw [Category.assoc, source, source, ← Category.assoc, ← HomologicalComplex.comp_f,
    SmallRefinementComparison.refinement_inclusion]

variable (hA : IsOpen A) (hA' : IsOpen A') (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (hc' : A' ∪ B = Set.univ)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) X (d + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) φ = 0)
  (hs' : cochainPullback (SupportedCap.subspaceMap X A') (d + 1) φ = 0)
  (hφ : cochainCoboundary (ZMod 2) X (d + 1) φ = 0)
  {Z : TopCat.{0}} (f₀ f₁ : Z ⟶ X) (H : Homotopy (push f₀) (push f₁)) (C : Set X)
  (hC : cochainPullback (SupportedCap.subspaceMap X C) (d + 1) φ = 0)
  (hf₀ : ∀ z, f₀ z ∈ C) (hf₁ : ∀ z, f₁ z ∈ C)

include hAA in
theorem homology_eq (q : ℕ) :
    (SupportedThomTime.operation X A B hA hB hc d φ hs hφ f₀ f₁ H C C hC hC hf₀ hf₁).homology q =
    (SupportedThomTime.operation X A' B hA' hB hc' d φ hs' hφ f₀ f₁ H C C hC hC hf₀ hf₁).homology q := by
  apply SingleCapTimeRetraction.homology_eq
    (SupportedCap.cover X A' B) (SupportedCap.cover X A B) id (cover_refines X A B A' hAA)
    (SupportedCap.cover_open X A' B hA' hB) (SupportedCap.cover_univ X A' B hc')
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hc)
    Z f₀ f₁ H (chains (TopCat.of B)) d
    (localized X A' B (d + 1) φ hs' hφ) (localized X A B (d + 1) φ hs hφ)
    (component X A B A' hAA (d + 1) · φ hs hs' hφ)
  · intro k
    rw [SupportedThomTime.component]
    rfl
  · intro k
    rw [SupportedThomTime.component]
    rfl

end
end Finsler.SupportedThomTimeRefinement
