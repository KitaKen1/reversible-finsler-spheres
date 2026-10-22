module

public import Finsler.Loop.FullSecondHalfNativeLift
public import Finsler.Topology.CutDomainTimePrism
public import Finsler.Topology.JoinedSimultaneousPrisms

/-! Actual annular inputs for the full, untrimmed native second-half
time operation. Both endpoint distances are literally zero. The Thom
pullback vanishes on its actual inner collar, and the bounded source
projection is monic on chains before retaining loops. -/

@[expose] public section
namespace Finsler.FullSecondHalfAnnularInputs

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.SecondHalfZeroFaceGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem faceCover_open (X : Type) [PseudoMetricSpace X] (η : ℝ) (center : Outer X) :
    IsOpen (SecondHalfNativeFaceCapDomain.faceCover X η center) :=
  (JoinedSimultaneousPrisms.rectangles_open X η center).preimage (planeFace (TopCat.of X) 1).hom.continuous

theorem faceCover_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ center, SecondHalfNativeFaceCapDomain.faceCover X η center = Set.univ := by
  simp only [SecondHalfNativeFaceCapDomain.faceCover, DoubleCapEmbeddingPullback.cover]
  rw [← Set.preimage_iUnion, JoinedSimultaneousPrisms.rectangles_univ X η hη, Set.preimage_univ]

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n))

def collar (δ : ℝ) : Set (ClosedInterval × X) :=
  JoinedHalfCollars.secondFamily u ⁻¹' {z | distance n z ≤ δ}

theorem thom_pullback (k : ℕ) (φ : singularCochainGroup (ZMod 2) (parameters n) k) :
    cochainPullback (planeFace (TopCat.of X) 1) k
      (SupportedSelfCutAdequacy.extension (tube X) (family u 0 (by norm_num) (by norm_num)) 2 k φ) =
      cochainPullback (JoinedHalfCollars.secondFamily u) k φ := by
  rw [JoinedFamilyNaturality.extension_eq_pullback, ← pullback_comp, face_family u]

theorem annular_inner_zero (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (collar u δ)) n
      (cochainPullback (planeFace (TopCat.of X) 1) n
        (SupportedSelfCutAdequacy.extension (tube X) (family u 0 (by norm_num) (by norm_num)) 2 n
          (AnnularSelfCut.cocycle n hn h))) = 0 := by
  rw [thom_pullback u n (AnnularSelfCut.cocycle n hn h)]
  exact pullback_support (JoinedHalfCollars.secondFamily u)
    (collar u δ) {z | distance n z ≤ δ} (fun _ hz => hz) n
    (AnnularSelfCut.cocycle n hn h) (AnnularSelfCut.cocycle_small_zero n hn h)

theorem distance_zero (x : X) : distance n (JoinedHalfCollars.secondFamily u (0, x)) = 0 := by
  change distance n (JoinedHalfCollars.second (0, u x)) = 0
  rw [JoinedHalfCollars.second_distance]
  exact UniformSelfCutCollar.distance_zero (JoinedHalfCollars.rightLoop u) x

theorem distance_one (x : X) : distance n (JoinedHalfCollars.secondFamily u (1, x)) = 0 := by
  change distance n (JoinedHalfCollars.second (1, u x)) = 0
  rw [JoinedHalfCollars.second_distance]
  exact UniformSelfCutCollar.distance_one (JoinedHalfCollars.rightLoop u) x

theorem projection_mono {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) (q : ℕ) :
    Mono ((push (FullSecondHalfNativeLift.nativeSource u hr F B)).f q) := by
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (nativeDomain u r))
      (nativeBounded u hr F B))).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (nativeDomain u r)) (nativeBounded u hr F B) q
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X))
      (nativeDomain u r))).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (ClosedInterval × X)) (nativeDomain u r) q
  rw [FullSecondHalfNativeLift.nativeSource, push_comp, HomologicalComplex.comp_f]
  infer_instance

end
end Finsler.FullSecondHalfAnnularInputs
