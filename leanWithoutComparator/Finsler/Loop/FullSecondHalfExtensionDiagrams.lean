module

public import Finsler.Loop.PartialTestedPullback
public import Finsler.Loop.FullSecondHalfCompactTimeOperation
public import Finsler.Loop.JoinTimeCommonRefinement

/-! Actual full-cylinder Thom and tested zero-extension pullbacks for
the original first-corrected second half. These are equalities on the
whole native cylinder, not only on the bounded cut domain. -/

@[expose] public section
namespace Finsler.FullSecondHalfExtensionDiagrams

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

theorem native_tested {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) {r : ℝ} (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    FullSecondHalfNativeTimeOperation.tested u hr p T =
      PartialTestedPullback.canonical (JoinedHalfCollars.secondFamily u) hr p T := by
  let O : TopCat.{0} := TopCat.of (Outer X)
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let f : C ⟶ TopCat.of (tube X) := planeFace (TopCat.of X) 1 ≫ UnivCochainExtension.lift O
  have hf : f ≫ SupportedCap.subspaceMap O (tube X) = planeFace (TopCat.of X) 1 := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have he : f ≫ family u 0 (by norm_num) (by norm_num) 2 = JoinedHalfCollars.secondFamily u := by
    rw [show f = planeFace (TopCat.of X) 1 ≫ UnivCochainExtension.lift O from rfl, Category.assoc]
    exact SecondHalfZeroFaceGeometry.face_family u
  have hh := PartialTestedPullback.pullback_tested (tube X)
    (family u 0 (by norm_num) (by norm_num)) 2 C f r hr p T
  rw [hf, he] at hh
  exact hh

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R < 1)

theorem thom_pullback (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (JoinTimeCommonRefinement.source α β R) n
      (SupportedSelfCutAdequacy.extension (OriginalSecondHalfCompactTube.tube α β R)
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
          (OriginalSecondHalfCompactTube.near α β R hR)) PUnit.unit n
        (AnnularSelfCut.cocycle n hn h)) =
      FullSecondHalfNativeTimeOperation.thom (CompactNearJoinParameters.inputs α β R hR) hn h := by
  unfold SupportedSelfCutAdequacy.extension JoinTimeCommonRefinement.source
  rw [pullback_comp, TubeCochainExtension.restriction, ← pullback_comp,
    CompactNearJoinParameters.second_family]
  exact (FullSecondHalfAnnularInputs.thom_pullback (CompactNearJoinParameters.inputs α β R hR)
    n (AnnularSelfCut.cocycle n hn h)).symm

theorem tested_pullback {r : ℝ} (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (JoinTimeCommonRefinement.source α β R) p
      (testedExtension (OriginalSecondHalfCompactTube.tube α β R)
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
          (OriginalSecondHalfCompactTube.near α β R hR)) (fun _ => r) (fun _ => hr) PUnit.unit p T) =
      FullSecondHalfNativeTimeOperation.tested (CompactNearJoinParameters.inputs α β R hR) hr p T := by
  rw [native_tested]
  have hh := PartialTestedPullback.pullback_tested (OriginalSecondHalfCompactTube.tube α β R)
    (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR)) PUnit.unit
    (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (CompactNearJoinParameters.timeMap α β R) r hr p T
  rw [CompactNearJoinParameters.second_family] at hh
  exact hh

end
end Finsler.FullSecondHalfExtensionDiagrams
