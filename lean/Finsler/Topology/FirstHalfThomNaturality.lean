module

public import Finsler.Topology.FirstHalfInteriorFamily

/-! The actual first-half self-evaluation is literally that of the first
input, on the entire cylinder. Thus the original annular Thom cochain
pulls back identically, including after the actual interior trimming. -/

@[expose] public section
namespace Finsler.FirstHalfThomNaturality

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.H1FiberBase Finsler.H1SelfCutNeighborhood Finsler.CompactH1Alignment
open Finsler.SelfCutThomCocycle Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

def joinedFirst (n : ℕ) : TopCat.of (ClosedInterval × H1JoinContinuity.composable n) ⟶ parameters n :=
  TopCat.ofHom ⟨JoinedHalfCollars.first, JoinedHalfCollars.continuous_first⟩

def firstProjection (n : ℕ) : TopCat.of (ClosedInterval × H1JoinContinuity.composable n) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.val.1),
    continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))⟩

theorem evaluation (n : ℕ) : joinedFirst n ≫ selfEvaluation n = firstProjection n ≫ selfEvaluation n := by
  apply TopCat.ext
  intro z
  apply Prod.ext
  · apply Subtype.ext
    change basepoint (JoinedHalfCollars.pairJoin z.2) = basepoint z.2.val.1
    exact H1LoopJoin.basepoint_join (1 / 2) (by norm_num) (by norm_num) _ _ z.2.property
  · apply Subtype.ext
    change continuousRepresentative ((JoinedHalfCollars.pairJoin z.2).data : Space n)
      (HalfConcatRestriction.half z.1) = continuousRepresentative (z.2.val.1.data : Space n) z.1
    exact HalfConcatRestriction.evaluate _ _ z.1

theorem diagonal_pullback (n p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (DiagonalCohomology.product n) p) :
    cochainPullback (joinedFirst n) p (cochainPullback (selfEvaluation n) p φ) =
      cochainPullback (firstProjection n) p (cochainPullback (selfEvaluation n) p φ) := by
  rw [← pullback_comp, ← pullback_comp, evaluation]

theorem annular_pullback (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (joinedFirst n) n (AnnularSelfCut.cocycle n hn h) =
      cochainPullback (firstProjection n) n (AnnularSelfCut.cocycle n hn h) :=
  diagonal_pullback n n (AnnularThomCocycle.ambient n hn h)

theorem trimmed_evaluation {X : Type} [TopologicalSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) :
    CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le ≫ selfEvaluation n =
      TopCat.ofHom (FirstHalfInteriorFamily.firstParameters u a ha ha1) ≫ selfEvaluation n := by
  let g : TopCat.of (ClosedInterval × X) ⟶ TopCat.of (ClosedInterval × H1JoinContinuity.composable n) :=
    TopCat.ofHom ⟨fun z => (InteriorTimeSlide.trimTime a ha.le ha1.le z.1, u z.2),
      ((InteriorTimeSlide.trimTime a ha.le ha1.le).continuous.comp continuous_fst).prodMk
        (u.continuous.comp continuous_snd)⟩
  have hj : g ≫ joinedFirst n = CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le := rfl
  have hp : g ≫ firstProjection n = TopCat.ofHom (FirstHalfInteriorFamily.firstParameters u a ha ha1) := rfl
  simpa only [← Category.assoc, hj, hp] using congrArg (fun f => g ≫ f) (evaluation n)

theorem trimmed_annular {X : Type} [TopologicalSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) n
      (AnnularSelfCut.cocycle n hn h) =
      cochainPullback (TopCat.ofHom (FirstHalfInteriorFamily.firstParameters u a ha ha1)) n
        (AnnularSelfCut.cocycle n hn h) := by
  change cochainPullback _ n (cochainPullback (selfEvaluation n) n _) =
    cochainPullback _ n (cochainPullback (selfEvaluation n) n _)
  rw [← pullback_comp, ← pullback_comp, trimmed_evaluation]

end
end Finsler.FirstHalfThomNaturality
