module

public import Finsler.Topology.UnivCochainExtension
public import Finsler.Topology.DoubleCapLocalBoundary
public import Finsler.Topology.JoinedRectangleRefinement

/-! The genuine three-family far cochain is globally closed when the
original cochain is closed. The tested zero extension is only locally
closed. Their actual successive caps commute with boundary on a common
rectangle refinement of the actual far/cut-domain covers. -/

@[expose] public section
namespace Finsler.JoinedCochainBoundary

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)

theorem extension_closed (i : Fin 3) (k : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) k)
    (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (Outer X)) k
      (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ) = 0 := by
  apply UnivCochainExtension.extend_closed
  exact CochainClass.closed_map (cochainCxZMod2 (parameters n))
    (singularCochainComplexZMod2.map (family u a ha ha1 i).op) k φ hφ

theorem extension_far_zero (ρ : ℝ) (i : Fin 3) (k : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (Outer X))
      (JoinedRectangleRefinement.far u a ha ha1 ρ i)) k
      (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ) = 0 := by
  apply SSet.chainComplex_hom_ext
    (X := TopCat.toSSet.obj (TopCat.of (JoinedRectangleRefinement.far u a ha ha1 ρ i))) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj (TopCat.of (JoinedRectangleRefinement.far u a ha ha1 ρ i))).ιChainComplex σ ≫
    ((push (SupportedCap.subspaceMap (TopCat.of (Outer X))
      (JoinedRectangleRefinement.far u a ha ha1 ρ i))).f k ≫
      SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ) = 0
  rw [push, SSet.ι_chainComplexMap_f_assoc]
  by_contra hnonzero
  obtain ⟨z, hz, hd⟩ := SupportedSelfCutAdequacy.witness (tube X) (family u a ha ha1) ρ i k φ hφ
    ((TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of (Outer X))
      (JoinedRectangleRefinement.far u a ha ha1 ρ i))).app _ σ) hnonzero
  have hf := TubeCochainExtension.included_range (TopCat.of (Outer X))
    (JoinedRectangleRefinement.far u a ha ha1 ρ i) σ hz
  change ρ < distanceValue (tube X) (family u a ha ha1) i z at hf
  linarith

theorem tested_closed (r : ℝ) (hr : r ≤ 1) (i : Fin 3) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (domain (tube X) (family u a ha ha1) (fun _ => r) i)) p
      (cochainPullback (testedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i) p T) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (TopCat.of (SphereLoop n)))
    (singularCochainComplexZMod2.map (testedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i).op) p T hT

theorem boundary (η ρ r : ℝ) (hr : r ≤ 1) (i : Fin 3)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ i ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i)
    (k p : ℕ) (φ : singularCochainGroup (ZMod 2) (parameters n) k)
    (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0)
    (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    ((inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f (k + (p + (q + 1))) ≫
      PartialDoubleCap.cap (TopCat.of (Outer X)) k p (q + 1)
        (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
        (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T)) ≫
      (chains (TopCat.of (Outer X))).d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
        (k + (p + (q + 1))) (k + (p + q)) ≫
      ((inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f (k + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (Outer X)) k p q
          (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
          (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T)) :=
  DoubleCapLocalBoundary.boundary_on_tube_cover (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)
    (JoinedRectangleRefinement.far u a ha ha1 ρ i) (domain (tube X) (family u a ha ha1) (fun _ => r) i)
    hW k p _ (extension_closed u a ha ha1 i k φ hφ) (extension_far_zero u a ha ha1 ρ i k φ hfar)
    _ (tested_closed u a ha ha1 r hr i p T hT) q

end
end Finsler.JoinedCochainBoundary
