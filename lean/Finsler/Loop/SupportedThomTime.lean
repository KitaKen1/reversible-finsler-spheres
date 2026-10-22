module

public import Finsler.Topology.DegreeLoweringSuccAlignment
public import Finsler.Topology.SelfCutEndpoints
public import Finsler.Topology.TimePrismDescent

/-! Genuine time descent of a supported closed cap with actual vanishing
on both endpoint subsets. The target is the specified near subspace. -/

@[expose] public section
namespace Finsler.SupportedThomTime

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) X (d + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) φ = 0)
  (hφ : cochainCoboundary (ZMod 2) X (d + 1) φ = 0)

def aligned := DegreeLoweringSuccAlignment.align d
  (SupportedCapHomology.operation X A B hA hB hc (d + 1) φ hs hφ) rfl

theorem comm (q : ℕ) : aligned X A B hA hB hc d φ hs hφ (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
    (chains X).d (d + q + 2) (d + q + 1) ≫ aligned X A B hA hB hc d φ hs hφ q :=
  DegreeLoweringSuccAlignment.comm d _ rfl q

include hs in
theorem endpoint {Z : TopCat.{0}} (f : Z ⟶ X) (C : Set X)
    (hC : cochainPullback (SupportedCap.subspaceMap X C) (d + 1) φ = 0) (hf : ∀ z, f z ∈ C) (q : ℕ) :
    (push f).f (d + q + 1) ≫ aligned X A B hA hB hc d φ hs hφ q = 0 := by
  exact DegreeLoweringSuccAlignment.pre_zero d _ rfl (push f) q
    (SelfCutEndpoints.cut_map_zero A B C hA hB hc (d + 1) q φ hs hC f hf)

variable {Z : TopCat.{0}} (f₀ f₁ : Z ⟶ X) (H : Homotopy (push f₀) (push f₁))
  (C₀ C₁ : Set X)
  (h₀ : cochainPullback (SupportedCap.subspaceMap X C₀) (d + 1) φ = 0)
  (h₁ : cochainPullback (SupportedCap.subspaceMap X C₁) (d + 1) φ = 0)
  (hf₀ : ∀ z, f₀ z ∈ C₀) (hf₁ : ∀ z, f₁ z ∈ C₁)

def operation := TimePrismDescent.operation H d (aligned X A B hA hB hc d φ hs hφ)
  (comm X A B hA hB hc d φ hs hφ)
  (endpoint X A B hA hB hc d φ hs hφ f₀ C₀ h₀ hf₀)
  (endpoint X A B hA hB hc d φ hs hφ f₁ C₁ h₁ hf₁)

theorem component (q : ℕ) :
    (operation X A B hA hB hc d φ hs hφ f₀ f₁ H C₀ C₁ h₀ h₁ hf₀ hf₁).component q =
    H.hom (d + q) (d + q + 1) ≫ eqToHom (congrArg (chains X).X
      (show d + q + 1 = (d + 1) + q by omega)) ≫
      SupportedCap.cut X A B hA hB hc (d + 1) q ((d + 1) + q) rfl φ hs := rfl

end
end Finsler.SupportedThomTime
