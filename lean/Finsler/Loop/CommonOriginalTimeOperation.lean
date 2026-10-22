module

public import Finsler.Loop.CommonOriginalTripleCap
public import Finsler.Loop.OriginalTimeCapRefinement
import all Finsler.Topology.OriginalSecondHalfTimeOperation

/-! The actual common-cover three-cap descends through the full original
time prism. Its actual endpoint zero comes from the annular Thom data.
Compare it with every original bounded lift on the original factor
cover, in the identical bounded cut target, using the relative prism. -/

@[expose] public section
namespace Finsler.CommonOriginalTimeOperation

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

private theorem map_ext {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f g : DegreeLoweringHomology.Map C E d) (h : ∀ q, f.component q = g.component q) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := funext h
      cases he
      rfl

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ) (hR : R < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (m + 1)) (B η σ κ : ℝ)
  (hκ : 0 < κ) (hκR : κ < R) (hη : 0 < η) (hσ : 0 < σ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X ((m + 1) + (p + q)) ⟶
      (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
        (CompactNearJoinParameters.inputs α β R hR) hr F B))).X q)
  (hc : ∀ q, c (q + 1) ≫ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
      (CompactNearJoinParameters.inputs α β R hR) hr F B))).d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)

def NativeSource : Prop := ∀ q, c q ≫ (push (FullSecondHalfNativeLift.nativeSource
    (CompactNearJoinParameters.inputs α β R hR) hr F B)).f q =
    (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f ((m + 1) + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (m + 1) p q
          (FullSecondHalfNativeTimeOperation.thom (CompactNearJoinParameters.inputs α β R hR) (by omega) h)
          (FullSecondHalfNativeTimeOperation.tested (CompactNearJoinParameters.inputs α β R hR) hr p T)

def cap : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ))
    (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))) ((m + 1) + (m + 1) + p) :=
  CommonOriginalTripleCap.operation α β R hR r hr F B η σ κ (by omega) hκ p c hc

theorem cap_source (hi : NativeSource α β R hR r hr F B η h p T c) :
    OriginalTimeCapRefinement.Source α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
      (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T (OriginalNativeCommonCover.cover α β R η σ κ)
      (cap α β R hR r hr F B η σ κ hκ p c hc) :=
  CommonOriginalTripleCap.source α β R hR r hr F B η σ κ (by omega) hκ p c hc h T hi

def operation (hi : NativeSource α β R hR r hr F B η h p T c) :
    DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))) ((m + 1) + m + p) :=
  OriginalSecondHalfTimeOperation.operation α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR) h (m + 1) p
    (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T (cap α β R hR r hr F B η σ κ hκ p c hc)
    (cap_source α β R hR r hr F B η σ κ hκ h p T c hc hi)

variable (hi : NativeSource α β R hR r hr F B η h p T c)
  (u : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.oldCover α β σ κ))
    (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))) ((m + 1) + (m + 1) + p))
  (hu : OriginalTimeCapRefinement.Source α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
    (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T (OriginalNativeCommonCover.oldCover α β σ κ) u)

include hi hu in
theorem cap_eq_refined : cap α β R hR r hr F B η σ κ hκ p c hc =
    OriginalTimeCapRefinement.refined α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B (m + 1) p
      (OriginalNativeCommonCover.oldCover α β σ κ) u (OriginalNativeCommonCover.cover α β R η σ κ)
      Prod.snd (fun _ _ hz => hz.2) := by
  apply map_ext
  intro q
  haveI := OriginalSecondHalfCapUniqueness.source_mono α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B q
  apply (cancel_mono ((push (OriginalSecondHalfBoundedFactors.source α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B)).f q)).mp
  dsimp only [OriginalTimeCapRefinement.refined, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, hu q, ← Category.assoc, ← HomologicalComplex.comp_f,
    SmallRefinementComparison.refinement_inclusion]
  exact (cap_source α β R hR r hr F B η σ κ hκ h p T c hc hi) q

theorem homology_eq (q : ℕ) :
    (operation α β R hR r hr F B η σ κ hκ hκR hη hσ h p T c hc hi).homology q =
      (OriginalSecondHalfTimeOperation.operation α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r hr F B
        (OriginalNativeCommonCover.oldCover α β σ κ) (OriginalNativeCommonCover.oldCover_open α β σ κ)
        (OriginalNativeCommonCover.oldCover_univ α β σ κ hσ hκ) h (m + 1) p
        (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T u hu).homology q := by
  have heq := cap_eq_refined α β R hR r hr F B η σ κ hκ h p T c hc hi u hu
  have hold := OriginalTimeCapRefinement.homology_eq α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
    (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T
    (OriginalNativeCommonCover.oldCover α β σ κ) (OriginalNativeCommonCover.oldCover_open α β σ κ)
    (OriginalNativeCommonCover.oldCover_univ α β σ κ hσ hκ) u hu
    (OriginalNativeCommonCover.cover α β R η σ κ) Prod.snd (fun _ _ hz => hz.2)
    (OriginalNativeCommonCover.cover_open α β R η σ κ)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR) q
  apply Eq.trans _ hold.symm
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro t
  have hnew := OriginalTimeCapRefinement.component_normal α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
    (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR)
    (cap α β R hR r hr F B η σ κ hκ p c hc)
    (cap_source α β R hR r hr F B η σ κ hκ h p T c hc hi) t
  change (operation α β R hR r hr F B η σ κ hκ hκR hη hσ h p T c hc hi).component t = _ at hnew
  rw [hnew, heq]
  exact (OriginalTimeCapRefinement.component_normal α β (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
    (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR)
    (OriginalTimeCapRefinement.refined α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B (m + 1) p
      (OriginalNativeCommonCover.oldCover α β σ κ) u (OriginalNativeCommonCover.cover α β R η σ κ)
      Prod.snd (fun _ _ hz => hz.2))
    (OriginalTimeCapRefinement.refined_source α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
      (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T
      (OriginalNativeCommonCover.oldCover α β σ κ) u hu (OriginalNativeCommonCover.cover α β R η σ κ)
      Prod.snd (fun _ _ hz => hz.2)) t).symm

end
end Finsler.CommonOriginalTimeOperation
