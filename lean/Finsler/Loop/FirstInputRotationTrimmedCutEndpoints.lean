module

public import Finsler.Loop.FirstInputRotationTrimmedEndpoints

/-! Keep the actual trimmed rotation endpoint before applying the
retained map. Its component formula retains the genuine retraction on
the whole target cylinder, as needed by relative source comparison. -/

@[expose] public section
namespace Finsler.FirstInputRotationTrimmedCutEndpoints

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCutCylinder Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

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
      (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) (m + p) :=
  (FirstInputRotationTrimmedTime.operation α β R r hR hr p T h F B η hη hρr hgood hT
    a ha ha1 hzero hone).pre (push (FirstInputRotationTimeEndpoints.slice α β R s))

theorem component_normal (s : _root_.unitInterval) (q : ℕ) :
    (endpoint α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone s).component q =
      AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
        (push (rotationSlice α β R s ≫ trimMap α β R a ha ha1) ≫
          TauCeti.smallSingularRetraction (X := cylinder α β R) coeff (cover α β R r η ρ)
            (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)).f ((m + p) + q + 1) ≫
          ClosedCapDegreeTransport.align m p
            (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT) q := by
  change (push (FirstInputRotationTimeEndpoints.slice α β R s)).f ((m + p) + q) ≫
    (FirstInputRotationTrimmedTime.operation α β R r hR hr p T h F B η hη hρr hgood hT
      a ha ha1 hzero hone).component q = _
  rw [FirstInputRotationTrimmedTime.component_normal]
  simp only [push_comp, HomologicalComplex.comp_f, Category.assoc]
  have he := FirstInputRotationTimeEndpoints.slice_prism α β R s ((m + p) + q)
  have hret : FirstInputRotationFullTime.retracted α β R r hR hr p T h F B η hη hρr hgood hT =
      (fun q => (TauCeti.smallSingularRetraction (X := cylinder α β R) coeff (cover α β R r η ρ)
        (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)).f ((m + 1) + (p + q)) ≫
          FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT q) := rfl
  simp only [FirstInputRotationTrimmedTime.aligned, hret, ClosedCapFunctoriality.align_pre,
    Category.assoc]
  simpa only [rotationSlice, FirstInputRotationTimeEndpoints.cylinderSlice, Category.assoc] using
    congrArg (fun g => g ≫ (push (trimMap α β R a ha ha1)).f ((m + p) + q + 1) ≫
      (TauCeti.smallSingularRetraction (X := cylinder α β R) coeff (cover α β R r η ρ)
        (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)).f ((m + p) + q + 1) ≫
        ClosedCapDegreeTransport.align m p
          (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT) q) he

theorem retained_homology (s : _root_.unitInterval) (q : ℕ) :
    ((endpoint α β R r hR hr p T h F B η hη hρr hgood hT a ha ha1 hzero hone s).post
      (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B))).homology q =
      (FirstInputRotationTrimmedEndpoints.endpoint α β R r hR hr p T h F B η hη hρr hgood hT
        a ha ha1 hzero hone s).homology q := by
  simp only [endpoint, FirstInputRotationTrimmedEndpoints.endpoint,
    FirstInputRotationTrimmedTime.retainedOperation, DegreeLoweringHomology.Map.post_homology,
    DegreeLoweringHomology.Map.pre_homology, Category.assoc]

end
end Finsler.FirstInputRotationTrimmedCutEndpoints
