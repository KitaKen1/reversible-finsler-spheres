module

public import Finsler.Loop.FirstInputRotationTrimmedTime
public import Finsler.Loop.FirstInputRotationJoinedTime

/-! Actual trimmed rotation endpoint operations, compared through the
genuine full-time model in the identical retained target. The first
localized join cap may remain in front of the entire comparison. -/

@[expose] public section
namespace Finsler.FirstInputRotationTrimmedEndpoints

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCutCylinder Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (F : ReversibleMetric (m + 1))
  (B η : ℝ) (hη : 0 < η) (hρr : ρ < r)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
  (hzero : ∀ s x, sideHomotopy α β R a ha ha1 0 (s, x) ∈ collar α β R δ)
  (hone : ∀ s x, sideHomotopy α β R a ha ha1 1 (s, x) ∈ collar α β R δ)

def endpoint (s : _root_.unitInterval) :
    DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) :=
  (FirstInputRotationTrimmedTime.retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT
    a ha ha1 hzero hone).pre (push (FirstInputRotationTimeEndpoints.slice α β R s))

theorem full_trim_homology_eq (s : _root_.unitInterval) (q : ℕ) :
    (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F B η hη hρr hgood hT s).homology q =
      (endpoint α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone s).homology q := by
  rw [endpoint, FirstInputRotationTimeEndpoints.endpoint,
    DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology,
    FirstInputRotationTrimmedTime.retained_homology_eq α β R r hR hr p T h F B η hη hρr hgood hT
      a ha ha1 hzero hone]

theorem homology_eq (q : ℕ) :
    (endpoint α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone 0).homology q =
      (endpoint α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone 1).homology q := by
  rw [← full_trim_homology_eq, ← full_trim_homology_eq]
  exact FirstInputRotationTimeEndpoints.homology_eq α β R r hR hr p T h F B η hη hρr hgood hT q

theorem component_normal (s : _root_.unitInterval) (q : ℕ) :
    (endpoint α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone s).component q =
      AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
        (push (FirstInputRotationTimeEndpoints.cylinderSlice α β R s ≫ trimMap α β R a ha ha1)).f
          ((m + p) + q + 1) ≫
            FirstInputRotationTrimmedTime.aligned α β R r hR hr p T h F B η hη hρr hgood hT q ≫
              (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B)).f q := by
  change (push (FirstInputRotationTimeEndpoints.slice α β R s)).f ((m + p) + q) ≫
    ((FirstInputRotationTrimmedTime.operation α β R r hR hr p T h F B η hη hρr hgood hT
      a ha ha1 hzero hone).component q ≫ _) = _
  rw [FirstInputRotationTrimmedTime.component_normal]
  simp only [push_comp, HomologicalComplex.comp_f, Category.assoc]
  have he := FirstInputRotationTimeEndpoints.slice_prism α β R s ((m + p) + q)
  simpa only [Category.assoc] using congrArg (fun g => g ≫
    (push (trimMap α β R a ha ha1)).f ((m + p) + q + 1) ≫
      FirstInputRotationTrimmedTime.aligned α β R r hR hr p T h F B η hη hρr hgood hT q ≫
        (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B)).f q) he

def joined {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (s : _root_.unitInterval) :=
  DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR)
    (endpoint α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone s)

theorem joined_homology_eq {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (q : ℕ) :
    (joined α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone hκ hκR 0).homology q =
      (joined α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone hκ hκR 1).homology q := by
  simp only [joined, DegreeLoweringComposition.homology]
  rw [homology_eq]

theorem full_joined_trim_homology_eq {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R)
    (s : _root_.unitInterval) (q : ℕ) :
    (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F B η hη hρr hgood hT s).homology q =
      (joined α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone hκ hκR s).homology q := by
  simp only [FirstInputRotationJoinedTime.joined, joined, DegreeLoweringComposition.homology]
  rw [full_trim_homology_eq]

end
end Finsler.FirstInputRotationTrimmedEndpoints
