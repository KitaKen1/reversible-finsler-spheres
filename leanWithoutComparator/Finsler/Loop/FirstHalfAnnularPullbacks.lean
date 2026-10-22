module

public import Finsler.Topology.FirstHalfAnnularTimeDomain
public import Finsler.Loop.PartialTestedPullback

/-! Identify the original first-half source Thom and tested zero
extensions on the whole trimmed cylinder with their actual canonical
pullbacks. These statements are not restricted to bounded cut chains. -/

@[expose] public section
namespace Finsler.FirstHalfAnnularPullbacks

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SelfCutParameterFamily Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

theorem face_family :
    (planeFace (TopCat.of X) 1 ≫ UnivCochainExtension.lift (TopCat.of (Outer X))) ≫
      family u a ha.le ha1.le 1 =
        CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change JoinedHalfCollars.firstFamily u (InteriorTimeSlide.slide a ha.le ha1.le (1, z.1), z.2) = _
  rw [InteriorTimeSlide.slide_one]
  rfl

theorem thom_pullback (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    FirstHalfAnnularTimeDomain.thom u a ha ha1 hn h =
      cochainPullback (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) n
        (AnnularSelfCut.cocycle n hn h) := by
  unfold FirstHalfAnnularTimeDomain.thom SupportedSelfCutAdequacy.extension
  simp only [JoinedComparisonAdequacy.tube]
  rw [UnivCochainExtension.extend_pullback, ← pullback_comp]
  have he := face_family u a ha ha1
  simpa only [Category.assoc] using congrArg
    (fun f => cochainPullback f n (AnnularSelfCut.cocycle n hn h)) he

theorem tested_pullback {r : ℝ} (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    FirstHalfAnnularTimeDomain.tested u a ha ha1 hr p T =
      PartialTestedPullback.canonical
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) hr p T := by
  let O : TopCat.{0} := TopCat.of (Outer X)
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let f : C ⟶ TopCat.of (tube X) := planeFace (TopCat.of X) 1 ≫ UnivCochainExtension.lift O
  have hf : f ≫ SupportedCap.subspaceMap O (tube X) = planeFace (TopCat.of X) 1 := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have he : f ≫ family u a ha.le ha1.le 1 =
      CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le := face_family u a ha ha1
  have hh := PartialTestedPullback.pullback_tested (tube X) (family u a ha.le ha1.le) 1 C f r hr p T
  rw [hf, he] at hh
  exact hh

end
end Finsler.FirstHalfAnnularPullbacks
