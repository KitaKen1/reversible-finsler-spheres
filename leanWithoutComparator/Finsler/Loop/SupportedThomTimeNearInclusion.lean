module

public import Finsler.Loop.SupportedThomTimeRefinement
import all Finsler.Loop.SingleCapTimeRetraction

/-! Enlarge the actual near target of supported Thom TIME. The far
set and supported cocycle remain fixed; distinct genuine subdivisions
are compared by the existing relative time refinement theorem. -/

@[expose] public section
namespace Finsler.SupportedThomTimeNearInclusion
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def nearMap (X : TopCat.{0}) (B D : Set X) (hBD : B ⊆ D) : TopCat.of B ⟶ TopCat.of D :=
  TopCat.ofHom (ContinuousMap.inclusion hBD)

theorem inclusion_square (X : TopCat.{0}) (B D : Set X) (hBD : B ⊆ D) :
    push (nearMap X B D hBD) ≫ push (SupportedCap.subspaceMap X D) =
      push (SupportedCap.subspaceMap X B) := by
  rw [← push_comp]
  rfl

theorem refines (X : TopCat.{0}) (A B D : Set X) (hBD : B ⊆ D) (i : Bool) :
    SupportedCap.cover X A B i ⊆ SupportedCap.cover X A D i := by
  cases i
  · exact Set.Subset.rfl
  · exact hBD

theorem component (X : TopCat.{0}) (A B D : Set X) (hBD : B ⊆ D) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (SmallRefinementComparison.refinement (SupportedCap.cover X A B) (SupportedCap.cover X A D) id
      (refines X A B D hBD)).f (p + q) ≫
        (SupportedThomTimeRefinement.localized X A D p φ hs hφ).component q =
    (SupportedThomTimeRefinement.localized X A B p φ hs hφ).component q ≫
      (push (nearMap X B D hBD)).f q := by
  have : Mono ((push (SupportedCap.subspaceMap X D)).f q) := SupportedCap.subspacePush_mono X D q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X D)).f q)).mp
  have hi := congrArg (fun f => f.f q) (inclusion_square X B D hBD)
  simp only [HomologicalComplex.comp_f] at hi
  simp only [Category.assoc]
  rw [SupportedThomTimeRefinement.source, hi, SupportedThomTimeRefinement.source,
    ← Category.assoc, ← HomologicalComplex.comp_f, SmallRefinementComparison.refinement_inclusion]

theorem homology (X : TopCat.{0}) (A B D : Set X) (hBD : B ⊆ D)
    (hA : IsOpen A) (hB : IsOpen B) (hD : IsOpen D)
    (hcB : A ∪ B = Set.univ) (hcD : A ∪ D = Set.univ)
    (d : ℕ) (φ : singularCochainGroup (ZMod 2) X (d + 1))
    (hs : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X (d + 1) φ = 0)
    {Z : TopCat.{0}} (f₀ f₁ : Z ⟶ X) (H : Homotopy (push f₀) (push f₁)) (C : Set X)
    (hC : cochainPullback (SupportedCap.subspaceMap X C) (d + 1) φ = 0)
    (hf₀ : ∀ z, f₀ z ∈ C) (hf₁ : ∀ z, f₁ z ∈ C) (q : ℕ) :
    (SupportedThomTime.operation X A B hA hB hcB d φ hs hφ f₀ f₁ H C C hC hC hf₀ hf₁).homology q ≫
      HomologicalComplex.homologyMap (push (nearMap X B D hBD)) q =
    (SupportedThomTime.operation X A D hA hD hcD d φ hs hφ f₀ f₁ H C C hC hC hf₀ hf₁).homology q := by
  have h := SingleCapTimeRetraction.homology_eq
    (SupportedCap.cover X A B) (SupportedCap.cover X A D) id (refines X A B D hBD)
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hcB)
    (SupportedCap.cover_open X A D hA hD) (SupportedCap.cover_univ X A D hcD)
    Z f₀ f₁ H (chains (TopCat.of D)) d
    ((SupportedThomTimeRefinement.localized X A B (d + 1) φ hs hφ).post (push (nearMap X B D hBD)))
    (SupportedThomTimeRefinement.localized X A D (d + 1) φ hs hφ)
    (component X A B D hBD (d + 1) · φ hs hφ)
    (SupportedThomTime.operation X A D hA hD hcD d φ hs hφ f₀ f₁ H C C hC hC hf₀ hf₁)
    ((SupportedThomTime.operation X A B hA hB hcB d φ hs hφ f₀ f₁ H C C hC hC hf₀ hf₁).post
      (push (nearMap X B D hBD)))
    (fun k => by rw [SupportedThomTime.component]; rfl)
    (fun k => by
      change (SupportedThomTime.operation X A B hA hB hcB d φ hs hφ f₀ f₁ H C C hC hC hf₀ hf₁).component k ≫ _ = _
      rw [SupportedThomTime.component]
      simp only [Category.assoc]
      rfl) q
  rw [DegreeLoweringHomology.Map.post_homology] at h
  exact h.symm

end
end Finsler.SupportedThomTimeNearInclusion
