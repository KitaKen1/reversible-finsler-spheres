module

public import Finsler.Topology.FirstHalfNativeCapDeformation
public import Finsler.Topology.CutDomainTimePrism
public import Finsler.Topology.JoinedSimultaneousPrisms

/-! Actual geometric inputs for the first-half cut-domain time prism:
the annular Thom pullback vanishes on its real inner collar, the bounded
cut-domain projection is monic on chains, and the actual face cover is
open and full. -/

@[expose] public section
namespace Finsler.FirstHalfAnnularTimeInputs

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

theorem faceCover_open (X : Type) [PseudoMetricSpace X] (η : ℝ) (center : Outer X) :
    IsOpen (FirstHalfInteriorCapDomain.faceCover X η center) :=
  (JoinedSimultaneousPrisms.rectangles_open X η center).preimage (planeFace (TopCat.of X) 1).hom.continuous

theorem faceCover_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ center, FirstHalfInteriorCapDomain.faceCover X η center = Set.univ := by
  simp only [FirstHalfInteriorCapDomain.faceCover, DoubleCapEmbeddingPullback.cover]
  rw [← Set.preimage_iUnion, JoinedSimultaneousPrisms.rectangles_univ X η hη, Set.preimage_univ]

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

def collar (δ : ℝ) : Set (ClosedInterval × X) :=
  (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) ⁻¹'
    {z | distance n z ≤ δ}

theorem thom_pullback (k : ℕ) (φ : singularCochainGroup (ZMod 2) (parameters n) k) :
    cochainPullback (planeFace (TopCat.of X) 1) k
      (SupportedSelfCutAdequacy.extension (tube X) (family u a ha.le ha1.le) 1 k φ) =
      cochainPullback (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) k φ := by
  rw [JoinedFamilyNaturality.extension_eq_pullback, ← pullback_comp, JoinedEndpointMaps.first_end]

theorem annular_inner_zero (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (collar u a ha ha1 δ)) n
      (cochainPullback (planeFace (TopCat.of X) 1) n
        (SupportedSelfCutAdequacy.extension (tube X) (family u a ha.le ha1.le) 1 n
          (AnnularSelfCut.cocycle n hn h))) = 0 := by
  rw [thom_pullback u a ha ha1 n (AnnularSelfCut.cocycle n hn h)]
  exact pullback_support
    (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le)
    (collar u a ha ha1 δ) {z | distance n z ≤ δ} (fun _ hz => hz) n
    (AnnularSelfCut.cocycle n hn h) (AnnularSelfCut.cocycle_small_zero n hn h)

def projection {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F A ⟶ TopCat.of (ClosedInterval × X) :=
  SupportedCap.subspaceMap
    (TopCat.of ((planeFace (TopCat.of X) 1) ⁻¹'
      domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1))
    (FirstHalfBoundedCapDeformation.boundedSet u a ha ha1 hr F A) ≫
  SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X))
    ((planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)

theorem projection_mono {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) (q : ℕ) :
    Mono ((push (projection u a ha ha1 hr F A)).f q) := by
  let D := (planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1
  let B := FirstHalfBoundedCapDeformation.boundedSet u a ha ha1 hr F A
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of D) B)).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of D) B q
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) D)).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (ClosedInterval × X)) D q
  rw [projection, push_comp, HomologicalComplex.comp_f]
  infer_instance

end
end Finsler.FirstHalfAnnularTimeInputs
