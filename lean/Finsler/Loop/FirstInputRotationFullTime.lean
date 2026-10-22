module

public import Finsler.Loop.FirstInputRotationTimeCap

/-! The actual full cut-time prism descends already into the bounded
proper cut domain. Its endpoint restrictions vanish by the actual
annular collar, before the fixed retained output is applied. -/

@[expose] public section
namespace Finsler.FirstInputRotationFullTime

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCutCylinder

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

def retracted (q : ℕ) :
    (chains (cylinder α β R)).X ((m + 1) + (p + q)) ⟶
      (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)).X q :=
  CutDomainTimePrism.retracted (input α β R) (cover α β R r η ρ)
    (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)
    (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) m p
    (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT) q

theorem retracted_comm (q : ℕ) :
    retracted α β R r hR hr p T h F B η hη hρr hgood hT (q + 1) ≫
        (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)).d (q + 1) q =
      (chains (cylinder α β R)).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫
        retracted α β R r hR hr p T h F B η hη hρr hgood hT q :=
  CutDomainTimePrism.retracted_comm _ _ _ _ _ m p _
    (FirstInputRotationTimeCap.component_comm α β R r hR hr p T (by omega) h F B η hgood hT) q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (input α β R) t)).f ((m + p) + q + 1) ≫
      ClosedCapDegreeTransport.align m p
        (retracted α β R r hR hr p T h F B η hη hρr hgood hT) q = 0 := by
  apply CutDomainTimePrism.endpoint_zero (input α β R) (cover α β R r η ρ)
    (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)
    (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) m p
    (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT)
    (collar α β R δ) (thom α β R hR (by omega) h) (tested α β R r hR hr p T)
    (thom_inner_zero α β R hR (by omega) h)
    (push (FirstInputRotationTimeCap.source α β R r hR hr F B))
    (FirstInputRotationTimeCap.source_mono α β R r hR hr F B)
    (FirstInputRotationTimeCap.component_source α β R r hR hr p T (by omega) h F B η hgood hT) t
  rcases ht with rfl | rfl
  · exact collar_zero α β R h.1.le
  · exact collar_one α β R h.1.le

def operation : DegreeLoweringHomology.Map (chains (input α β R))
    (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) (m + p) :=
  CutDomainTimePrism.operation (input α β R) (cover α β R r η ρ)
    (cover_open α β R r η ρ) (cover_univ α β R r η hη hρr)
    (chains (FirstInputRotationTimeCap.target α β R r hR hr F B)) m p
    (FirstInputRotationTimeCap.component α β R r hR hr p T (by omega) h F B η hgood hT)
    (collar α β R δ) (thom α β R hR (by omega) h) (tested α β R r hR hr p T)
    (thom_inner_zero α β R hR (by omega) h)
    (push (FirstInputRotationTimeCap.source α β R r hR hr F B))
    (FirstInputRotationTimeCap.source_mono α β R r hR hr F B)
    (FirstInputRotationTimeCap.component_source α β R r hR hr p T (by omega) h F B η hgood hT)
    (FirstInputRotationTimeCap.component_comm α β R r hR hr p T (by omega) h F B η hgood hT)
    (collar_zero α β R h.1.le) (collar_one α β R h.1.le)

theorem component_normal (q : ℕ) :
    (operation α β R r hR hr p T h F B η hη hρr hgood hT).component q =
      AnnularTimeTrim.prism (input α β R) ((m + p) + q) ≫
        ClosedCapDegreeTransport.align m p
          (retracted α β R r hR hr p T h F B η hη hρr hgood hT) q := rfl

def retainedOperation : DegreeLoweringHomology.Map (chains (input α β R))
    (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) :=
  (operation α β R r hR hr p T h F B η hη hρr hgood hT).post
    (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B))

theorem retained_component_normal (q : ℕ) :
    (retainedOperation α β R r hR hr p T h F B η hη hρr hgood hT).component q =
      AnnularTimeTrim.prism (input α β R) ((m + p) + q) ≫
        ClosedCapDegreeTransport.align m p
          (retracted α β R r hR hr p T h F B η hη hρr hgood hT) q ≫
            (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B)).f q := rfl

end
end Finsler.FirstInputRotationFullTime
