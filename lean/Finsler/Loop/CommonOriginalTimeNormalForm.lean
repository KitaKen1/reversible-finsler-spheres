module

public import Finsler.Loop.CommonOriginalTimeOperation
public import Finsler.Loop.TimeCapOutputNaturality

/-! Put the genuine common original time operation into the native
join-first degree convention. Its normal form uses the actual native
raw cap followed by the actual bounded-domain isomorphism. -/

@[expose] public section
namespace Finsler.CommonOriginalTimeNormalForm

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

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

def posted (q : ℕ) :
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X ((m + 1) + (p + q)) ⟶
      (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))).X q :=
  c q ≫ (push (CommonOriginalTripleCap.toOld α β R hR r hr F B)).f q

include hc in
theorem posted_comm (q : ℕ) :
    posted α β R hR r hr F B η p c (q + 1) ≫
      (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))).d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ posted α β R hR r hr F B η p c q :=
  TimeCapOutputNaturality.raw_post_comm (m + 1) p c hc (push (CommonOriginalTripleCap.toOld α β R hR r hr F B)) q

theorem cap_posted :
    NativeCommonTripleCap.operation α β R η σ κ (by omega) hκ _ p
      (posted α β R hR r hr F B η p c) (posted_comm α β R hR r hr F B η p c hc) =
      (NativeCommonTripleCap.operation α β R η σ κ (by omega) hκ _ p c hc).post
        (push (CommonOriginalTripleCap.toOld α β R hR r hr F B)) := by
  apply map_ext
  intro q
  simp only [NativeCommonTripleCap.component, posted, DegreeLoweringHomology.Map.post, Category.assoc]

theorem cap_aligned (d : ℕ) (hm : (m + 1) + (m + 1) + p = d + 1) (q : ℕ) :
    DegreeLoweringSuccAlignment.align d (CommonOriginalTimeOperation.cap α β R hR r hr F B η σ κ hκ p c hc) hm q =
      DegreeLoweringSuccAlignment.align d
        (NativeCommonTripleCap.operation α β R η σ κ (by omega) hκ _ p
          (posted α β R hR r hr F B η p c) (posted_comm α β R hR r hr F B η p c hc)) (by omega) q := by
  rw [cap_posted, SuccAlignmentNaturality.post]
  dsimp only [CommonOriginalTimeOperation.cap, CommonOriginalTripleCap.operation]
  rw [SuccAlignmentNaturality.post, TimeCapOutputNaturality.align_regrade]

variable (hi : CommonOriginalTimeOperation.NativeSource α β R hR r hr F B η h p T c)

def operation : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))) ((m + 1) + (m + p)) :=
  DegreeLoweringRegrade.regrade
    (CommonOriginalTimeOperation.operation α β R hR r hr F B η σ κ hκ hκR hη hσ h p T c hc hi)
    ((m + 1) + (m + p)) (Nat.add_assoc (m + 1) m p).symm

theorem component (q : ℕ) :
    (operation α β R hR r hr F B η σ κ hκ hκR hη hσ h p T c hc hi).component q =
      (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom
        (((m + 1) + (m + p)) + q) (((m + 1) + (m + p)) + q + 1) ≫
      (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff
        (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
        (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR)).f
          (((m + 1) + (m + p)) + q + 1) ≫
      DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
        (NativeCommonTripleCap.operation α β R η σ κ (by omega) hκ _ p
          (posted α β R hR r hr F B η p c) (posted_comm α β R hR r hr F B η p c hc)) (by omega) q := by
  have he := TimeCapOutputNaturality.time_regrade_component
    (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q))
    (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff
      (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
      (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR))
    (CommonOriginalTimeOperation.cap α β R hR r hr F B η σ κ hκ p c hc) (by omega)
    (CommonOriginalTimeOperation.operation α β R hR r hr F B η σ κ hκ hκR hη hσ h p T c hc hi)
    (OriginalTimeCapRefinement.component_normal α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B h (m + 1) p
      (CompactJoinCocycle.timeCocycle α β (by omega) hκ) T
      (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
      (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR)
      (CommonOriginalTimeOperation.cap α β R hR r hr F B η σ κ hκ p c hc)
      (CommonOriginalTimeOperation.cap_source α β R hR r hr F B η σ κ hκ h p T c hc hi))
    ((m + 1) + (m + p)) (Nat.add_assoc (m + 1) m p).symm (by omega) q
  rw [cap_aligned] at he
  exact he

end
end Finsler.CommonOriginalTimeNormalForm
