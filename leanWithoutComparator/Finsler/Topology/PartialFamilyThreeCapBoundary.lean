module

public import Finsler.Topology.ThreeCapLocalBoundary
public import Finsler.Topology.SupportedSelfCutAdequacy

/-! The literal join/annular-cut/tested three-cap boundary equation for
an actual partial family on its original outer tube. The zero extensions
are only restricted to their genuine domains; they are not assumed
globally closed. -/

@[expose] public section
namespace Finsler.PartialFamilyThreeCapBoundary

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SelfCutParameterFamily
open Finsler.ThreeCapBlockVanishing
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {ι : Type*} {n : ℕ}
  (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n))
  (r : ι → ℝ) (hr : ∀ i, r i ≤ 1)

theorem extension_far_zero (ρ : ℝ) (i : ι) (b : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) b)
    (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) b φ = 0) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q))
      {z | ρ < distanceValue K e i z}) b (SupportedSelfCutAdequacy.extension K e i b φ) = 0 := by
  apply SSet.chainComplex_hom_ext
    (X := TopCat.toSSet.obj (TopCat.of ({z | ρ < distanceValue K e i z} : Set (P × Q)))) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj (TopCat.of ({z | ρ < distanceValue K e i z} : Set (P × Q)))).ιChainComplex σ ≫
    ((push (SupportedCap.subspaceMap (TopCat.of (P × Q)) {z | ρ < distanceValue K e i z})).f b ≫
      SupportedSelfCutAdequacy.extension K e i b φ) = 0
  rw [push, SSet.ι_chainComplexMap_f_assoc]
  by_contra hnz
  obtain ⟨z, hz, hd⟩ := SupportedSelfCutAdequacy.witness K e ρ i b φ hφ
    ((TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of (P × Q))
      {z | ρ < distanceValue K e i z})).app _ σ) hnz
  have hf := TubeCochainExtension.included_range (TopCat.of (P × Q))
    {z | ρ < distanceValue K e i z} σ hz
  change ρ < distanceValue K e i z at hf
  linarith

theorem extension_closed_on_domain (i : ι) (b : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) b)
    (hφ : cochainCoboundary (ZMod 2) (parameters n) b φ = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (domain K e r i)) b
      (cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q)) (domain K e r i)) b
        (SupportedSelfCutAdequacy.extension K e i b φ)) = 0 := by
  let g : TopCat.of (domain K e r i) ⟶ TopCat.of K :=
    TopCat.ofHom ⟨fun z => ⟨z.val, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  have he : g ≫ SupportedCap.subspaceMap (TopCat.of (P × Q)) K =
      SupportedCap.subspaceMap (TopCat.of (P × Q)) (domain K e r i) := by
    ext z : 1
    rfl
  unfold SupportedSelfCutAdequacy.extension
  rw [← he, pullback_comp, TubeCochainExtension.restriction, ← pullback_comp]
  exact CochainClass.closed_map (cochainCxZMod2 (parameters n))
    (singularCochainComplexZMod2.map (g ≫ e i).op) b φ hφ

theorem tested_closed_on_domain (i : ι) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (domain K e r i)) p
      (cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q)) (domain K e r i)) p
        (testedExtension K e r hr i p T)) = 0 := by
  unfold testedExtension
  rw [TubeCochainExtension.restriction]
  exact CochainClass.closed_map (cochainCxZMod2 (TopCat.of (SphereLoop n)))
    (singularCochainComplexZMod2.map (testedMap K e r hr i).op) p T hT

theorem boundary {κ : Type*} (W : κ → Set (P × Q)) (A : Set (P × Q)) (ρ : ℝ) (i : ι)
    (hW : ∀ v, W v ⊆ A ∨ W v ⊆ {z | ρ < distanceValue K e i z} ∨ W v ⊆ domain K e r i)
    (a b p : ℕ) (J : singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) a)
    (hJ : cochainCoboundary (ZMod 2) (TopCat.of (P × Q)) a J = 0)
    (hA : cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q)) A) a J = 0)
    (φ : singularCochainGroup (ZMod 2) (parameters n) b)
    (hφ : cochainCoboundary (ZMod 2) (parameters n) b φ = 0)
    (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) b φ = 0)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    ((inclusion (TopCat.of (P × Q)) W).f (a + b + p + (q + 1)) ≫
      threeCap (TopCat.of (P × Q)) a b p (q + 1) J
        (SupportedSelfCutAdequacy.extension K e i b φ) (testedExtension K e r hr i p T)) ≫
      (chains (TopCat.of (P × Q))).d (q + 1) q =
    (small (TopCat.of (P × Q)) W).d (a + b + p + (q + 1)) (a + b + p + q) ≫
      ((inclusion (TopCat.of (P × Q)) W).f (a + b + p + q) ≫
        threeCap (TopCat.of (P × Q)) a b p q J
          (SupportedSelfCutAdequacy.extension K e i b φ) (testedExtension K e r hr i p T)) := by
  apply ThreeCapLocalBoundary.boundary_of_parts
  apply ThreeCapLocalBoundary.cup_boundary_on_cover (TopCat.of (P × Q)) W A
    {z | ρ < distanceValue K e i z} (domain K e r i) hW a b p _ _ _ hA
    (extension_far_zero K e ρ i b φ hfar)
  · exact CochainClass.closed_map (cochainCxZMod2 (TopCat.of (P × Q)))
      (singularCochainComplexZMod2.map
        (SupportedCap.subspaceMap (TopCat.of (P × Q)) (domain K e r i)).op) a J hJ
  · exact extension_closed_on_domain K e r i b φ hφ
  · exact tested_closed_on_domain K e r hr i p T hT

end
end Finsler.PartialFamilyThreeCapBoundary
