module

public import Finsler.Topology.JoinedCochainBoundary

/-! The genuine full-domain three-family cochain is a literal ambient
pullback. The same actual map takes its far and cut-domain sets to the
original exterior and neighborhood; its domain restriction is the
existing actual toCut map. -/

@[expose] public section
namespace Finsler.JoinedFamilyNaturality

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SelfCutParameterFamily Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)

def globalMap (i : Fin 3) : TopCat.of (Outer X) ⟶ parameters n :=
  UnivCochainExtension.lift (TopCat.of (Outer X)) ≫ family u a ha ha1 i

theorem extension_eq_pullback (i : Fin 3) (k : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) k) :
    SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ =
      cochainPullback (globalMap u a ha ha1 i) k φ := by
  change TubeCochainExtension.extend (TopCat.of (Outer X)) Set.univ k
    (cochainPullback (family u a ha ha1 i) k φ) =
      cochainPullback (UnivCochainExtension.lift (TopCat.of (Outer X)) ≫ family u a ha ha1 i) k φ
  exact UnivCochainExtension.extend_pullback (X := TopCat.of (Outer X))
    (Y := parameters n) (family u a ha ha1 i) k φ

theorem distance_global (i : Fin 3) (z : Outer X) :
    distance n (globalMap u a ha ha1 i z) = distanceValue (tube X) (family u a ha ha1) i z := by
  rw [distanceValue, TubeTestWitness.partialValue]
  rw [dite_eq_left (show z ∈ tube X from Set.mem_univ z)]
  rfl

theorem far_maps (ρ : ℝ) (i : Fin 3) :
    Set.MapsTo (globalMap u a ha ha1 i) (JoinedRectangleRefinement.far u a ha ha1 ρ i) (exterior n ρ) := by
  intro z hz
  change ρ < distance n (globalMap u a ha ha1 i z)
  rw [distance_global]
  exact hz

theorem domain_maps (r : ℝ) (i : Fin 3) :
    Set.MapsTo (globalMap u a ha ha1 i)
      (domain (tube X) (family u a ha ha1) (fun _ => r) i) (neighborhood n r) := by
  intro z hz
  change distance n (globalMap u a ha ha1 i z) < r
  rw [distance_global]
  exact hz.2

theorem restriction_eq_toCut (r : ℝ) (i : Fin 3) :
    restriction (globalMap u a ha ha1 i) (domain (tube X) (family u a ha ha1) (fun _ => r) i)
      (neighborhood n r) (domain_maps u a ha ha1 r i) =
      toCut (tube X) (family u a ha ha1) (fun _ => r) i := by
  ext z : 1
  rfl

end
end Finsler.JoinedFamilyNaturality
