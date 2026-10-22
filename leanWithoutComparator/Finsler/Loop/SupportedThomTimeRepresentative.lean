module

public import Finsler.Loop.SupportedThomTime
public import Finsler.Loop.TimePrismCapCoboundaryAllDegrees
public import Finsler.Topology.SupportedCapRepresentative

/-! Relative representative comparison for the genuine time-supported
cap itself. The actual primitive vanishes at both endpoints; integrating
its literal coboundary gives an actual boundary in the same near target. -/

@[expose] public section
namespace Finsler.SupportedThomTimeRepresentative

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)

theorem cut_input (p q N : ℕ) (h : p + q = N) (φ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0) :
    eqToHom (congrArg (chains X).X h.symm) ≫ SupportedCap.cut X A B hA hB hc p q (p + q) rfl φ hs =
      SupportedCap.cut X A B hA hB hc p q N h φ hs := by
  subst N
  simp only [eqToHom_refl, Category.id_comp]

theorem aligned_cut (d q : ℕ) (φ : singularCochainGroup (ZMod 2) X (d + 1))
    (hs : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X (d + 1) φ = 0) :
    SupportedThomTime.aligned X A B hA hB hc d φ hs hφ q =
      SupportedCap.cut X A B hA hB hc (d + 1) q (d + q + 1) (by omega) φ hs :=
  cut_input X A B hA hB hc (d + 1) q (d + q + 1) (by omega) φ hs

variable (d : ℕ) (φ ψ : singularCochainGroup (ZMod 2) X (d + 1))
  (hφA : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) φ = 0)
  (hψA : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) ψ = 0)
  (hφ : cochainCoboundary (ZMod 2) X (d + 1) φ = 0)
  (hψ : cochainCoboundary (ZMod 2) X (d + 1) ψ = 0)
  (ξ : singularCochainGroup (ZMod 2) X d)
  (hξA : cochainPullback (SupportedCap.subspaceMap X A) d ξ = 0)
  (hδ : cochainCoboundary (ZMod 2) X d ξ = φ - ψ)

def primitiveCap (q : ℕ) := SupportedCap.cut X A B hA hB hc d q (d + q) rfl ξ hξA

include hδ in
theorem boundary (q : ℕ) :
    SupportedCap.cut X A B hA hB hc d (q + 1) (d + q + 1) (by omega) ξ hξA ≫ (chains (TopCat.of B)).d (q + 1) q =
    (chains X).d (d + q + 1) (d + q) ≫ primitiveCap X A B hA hB hc d ξ hξA q -
      (SupportedThomTime.aligned X A B hA hB hc d φ hφA hφ q -
        SupportedThomTime.aligned X A B hA hB hc d ψ hψA hψ q) := by
  have hs := SupportedCapRepresentative.support_sub X A (d + 1) φ ψ hφA hψA
  have hd : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) (cochainCoboundary (ZMod 2) X d ξ) = 0 := by
    rw [hδ]
    exact hs
  have he := SupportedCapCochain.cut_coboundary X A B hA hB hc d q (d + q) rfl ξ hξA hd
  have hcs := (SupportedCapRepresentative.cut_congr X A B hA hB hc (d + 1) q (d + q + 1) (by omega)
    _ _ hd hs hδ).trans (SupportedCapCochain.cut_sub X A B hA hB hc (d + 1) q (d + q + 1) (by omega) φ ψ hφA hψA hs)
  rw [hcs] at he
  rw [aligned_cut, aligned_cut]
  exact he

variable {Z : TopCat.{0}} (f₀ f₁ : Z ⟶ X) (H : Homotopy (push f₀) (push f₁)) (C : Set X)
  (hφC : cochainPullback (SupportedCap.subspaceMap X C) (d + 1) φ = 0)
  (hψC : cochainPullback (SupportedCap.subspaceMap X C) (d + 1) ψ = 0)
  (hξC : cochainPullback (SupportedCap.subspaceMap X C) d ξ = 0)
  (hf₀ : ∀ z, f₀ z ∈ C) (hf₁ : ∀ z, f₁ z ∈ C)

include hδ hξC hξA in
theorem homology_eq (q : ℕ) :
    (SupportedThomTime.operation X A B hA hB hc d φ hφA hφ f₀ f₁ H C C hφC hφC hf₀ hf₁).homology q =
    (SupportedThomTime.operation X A B hA hB hc d ψ hψA hψ f₀ f₁ H C C hψC hψC hf₀ hf₁).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (-(H.hom (d + q) (d + q + 1) ≫
      SupportedCap.cut X A B hA hB hc d (q + 1) (d + q + 1) (by omega) ξ hξA))
  have hb := boundary X A B hA hB hc d φ ψ hφA hψA hφ hψ ξ hξA hδ q
  have hz₀ := SelfCutEndpoints.cut_map_zero A B C hA hB hc d q ξ hξA hξC f₀ hf₀
  have hz₁ := SelfCutEndpoints.cut_map_zero A B C hA hB hc d q ξ hξA hξC f₁ hf₁
  have he := TimePrismCapCoboundaryAllDegrees.cycle_boundary H (d + q) q
    (primitiveCap X A B hA hB hc d ξ hξA q)
    (SupportedCap.cut X A B hA hB hc d (q + 1) (d + q + 1) (by omega) ξ hξA)
    (SupportedThomTime.aligned X A B hA hB hc d φ hφA hφ q -
      SupportedThomTime.aligned X A B hA hB hc d ψ hψA hψ q) hb hz₀ hz₁
    ((chains Z).iCycles (d + q)) ((chains Z).iCycles_d _ _)
  change (chains Z).iCycles (d + q) ≫
    ((H.hom (d + q) (d + q + 1) ≫ SupportedThomTime.aligned X A B hA hB hc d φ hφA hφ q) -
      (H.hom (d + q) (d + q + 1) ≫ SupportedThomTime.aligned X A B hA hB hc d ψ hψA hψ q)) = _
  rw [← Preadditive.comp_sub]
  simpa only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp] using he

end
end Finsler.SupportedThomTimeRepresentative
