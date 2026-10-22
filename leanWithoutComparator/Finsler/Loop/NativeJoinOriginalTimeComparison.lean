module

public import Finsler.Loop.CommonOriginalTimeNormalForm
public import Finsler.Loop.WholeIntervalRelativeHomology
public import Finsler.Loop.FullSecondHalfJoinTimeOperation

/-! Actual native join-first and common original full-time operations
agree on all input homology, in the same bounded cut domain and after
retaining in exactly the same length sublevel. -/

@[expose] public section
namespace Finsler.NativeJoinOriginalTimeComparison

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ) (hR : R < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (m + 1)) (B η σ κ : ℝ)
  (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hη : 0 < η) (hσ : 0 < σ)
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

variable (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
      (CompactNearJoinParameters.inputs α β R hR) hr F B))) (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
        (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη) _ m p c) q)

include hw in
theorem posted_time_component (q : ℕ) :
    (w.post (push (CommonOriginalTripleCap.toOld α β R hR r hr F B))).component q =
      AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
      ClosedCapDegreeTransport.align m p
        (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
          (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
          (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη) _ m p
          (CommonOriginalTimeNormalForm.posted α β R hR r hr F B η p c)) q := by
  change w.component q ≫ (push (CommonOriginalTripleCap.toOld α β R hR r hr F B)).f q = _
  rw [hw q]
  simp only [ClosedCapDegreeTransport.align, CutDomainTimePrism.retracted,
    CommonOriginalTimeNormalForm.posted, Category.assoc]

variable (hi : CommonOriginalTimeOperation.NativeSource α β R hR r hr F B η h p T c)

include hw in
theorem bounded_homology_eq (q : ℕ) :
    ((WholeIntervalJoinFirstIdentity.joined α β R κ hκ hκR _ p w).post
      (push (CommonOriginalTripleCap.toOld α β R hR r hr F B))).homology q =
      (CommonOriginalTimeNormalForm.operation α β R hR r hr F B η σ κ hκ (by linarith) hη hσ h p T c hc hi).homology q := by
  have he := WholeIntervalRelativeHomology.homology_eq α β R η σ κ hκ hκR hη hσ _ p
    (CommonOriginalTimeNormalForm.posted α β R hR r hr F B η p c)
    (CommonOriginalTimeNormalForm.posted_comm α β R hR r hr F B η p c hc)
    (w.post (push (CommonOriginalTripleCap.toOld α β R hR r hr F B)))
    (posted_time_component α β R hR r hr F B η hη p c w hw)
    (CommonOriginalTimeNormalForm.operation α β R hR r hr F B η σ κ hκ (by linarith) hη hσ h p T c hc hi)
    (CommonOriginalTimeNormalForm.component α β R hR r hr F B η σ κ hκ (by linarith) hη hσ h p T c hc hi) q
  dsimp only [WholeIntervalJoinFirstIdentity.joined] at he ⊢
  rw [TimeCapOutputNaturality.compose_post] at he
  exact he

include hw in
theorem retained_homology_eq (q : ℕ) :
    (FullSecondHalfJoinTimeOperation.joined α β (by omega) hκ hκR hR hr F B (m + p) w).homology q =
      ((CommonOriginalTimeNormalForm.operation α β R hR r hr F B η σ κ hκ (by linarith) hη hσ h p T c hc hi).post
        (push (OriginalSecondHalfBoundedFactors.retained α β (OriginalSecondHalfCompactTube.tube α β R)
          (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))).homology q := by
  have he := congrArg (fun f => f ≫ HomologicalComplex.homologyMap
    (push (OriginalSecondHalfBoundedFactors.retained α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B)) q)
    (bounded_homology_eq α β R hR r hr F B η σ κ hκ hκR hη hσ h p T c hc w hw hi q)
  rw [← DegreeLoweringHomology.Map.post_homology, ← DegreeLoweringHomology.Map.post_homology] at he
  apply Eq.trans _ he
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro t
  simp only [FullSecondHalfJoinTimeOperation.joined, WholeIntervalJoinFirstIdentity.joined,
    DegreeLoweringHomology.Map.post, Category.assoc]
  rw [← HomologicalComplex.comp_f, ← push_comp, CommonOriginalTripleCap.retained_square]

end
end Finsler.NativeJoinOriginalTimeComparison
