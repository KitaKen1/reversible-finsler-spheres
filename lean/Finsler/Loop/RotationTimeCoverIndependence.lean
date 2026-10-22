module

public import Finsler.Loop.CommonRegradedCapTime
public import Finsler.Loop.NestedCapTimeSingleSource
public import Finsler.Loop.FirstInputRotationJoinedTime

/-! Independent rotating cap-time covers and their actual adequacy
witnesses give the same genuine bounded, retained, endpoint and joined
homology operations. The original R/kappa and output target stay fixed. -/

@[expose] public section
namespace Finsler.RotationTimeCoverIndependence

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.FirstInputRotationCutCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (F : ReversibleMetric (m + 1))
  (B η₀ η₁ : ℝ) (hη₀ : 0 < η₀) (hη₁ : 0 < η₁) (hρr : ρ < r)
  (g₀ : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η₀ p T)
  (g₁ : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η₁ p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem bounded_homology (q : ℕ) :
    (FirstInputRotationFullTime.operation α β R r hR hr p T h F B η₀ hη₀ hρr g₀ hT).homology q =
    (FirstInputRotationFullTime.operation α β R r hR hr p T h F B η₁ hη₁ hρr g₁ hT).homology q := by
  let X := input α β R
  let E := chains (FirstInputRotationTimeCap.target α β R r hR hr F B)
  let U := cover α β R r η₀ ρ
  let V := cover α β R r η₁ ρ
  let C := collar α β R δ
  let φ := thom α β R hR (show 1 ≤ m + 1 by omega) h
  let ψ := tested α β R r hR hr p T
  let j := push (FirstInputRotationTimeCap.source α β R r hR hr F B)
  let c₀ := FirstInputRotationTimeCap.component α β R r hR hr p T (show 1 ≤ m + 1 by omega) h F B η₀ g₀ hT
  let c₁ := FirstInputRotationTimeCap.component α β R r hR hr p T (show 1 ≤ m + 1 by omega) h F B η₁ g₁ hT
  let hc₀ := FirstInputRotationTimeCap.component_comm α β R r hR hr p T (show 1 ≤ m + 1 by omega) h F B η₀ g₀ hT
  let hc₁ := FirstInputRotationTimeCap.component_comm α β R r hR hr p T (show 1 ≤ m + 1 by omega) h F B η₁ g₁ hT
  let hi₀ := FirstInputRotationTimeCap.component_source α β R r hR hr p T (show 1 ≤ m + 1 by omega) h F B η₀ g₀ hT
  let hi₁ := FirstInputRotationTimeCap.component_source α β R r hR hr p T (show 1 ≤ m + 1 by omega) h F B η₁ g₁ hT
  let hj := FirstInputRotationTimeCap.source_mono α β R r hR hr F B
  let hφ := thom_inner_zero α β R hR (show 1 ≤ m + 1 by omega) h
  let hz₀ := collar_zero α β R h.1.le
  let hz₁ := collar_one α β R h.1.le
  have h₀ := NestedCapTimeSingleSource.time_homology X U (cover_open α β R r η₀ ρ)
    (cover_univ α β R r η₀ hη₀ hρr) E m p c₀ hc₀ C φ ψ hφ j hj hi₀ hz₀ hz₁ q
  have h₁ := NestedCapTimeSingleSource.time_homology X V (cover_open α β R r η₁ ρ)
    (cover_univ α β R r η₁ hη₁ hρr) E m p c₁ hc₁ C φ ψ hφ j hj hi₁ hz₀ hz₁ q
  have he := CommonRegradedCapTime.homology_eq X U V (cover_open α β R r η₀ ρ)
    (cover_univ α β R r η₀ hη₀ hρr) (cover_open α β R r η₁ ρ) (cover_univ α β R r η₁ hη₁ hρr)
    E (m + p) ((m + 1) + p) (by omega)
    (NestedCapTimeSingleSource.cap X U E m p c₀ hc₀) (NestedCapTimeSingleSource.cap X V E m p c₁ hc₁)
    C (NestedCapTimeSingleSource.cochain X m p φ ψ) (NestedCapTimeSingleSource.cochain_zero X m p C φ ψ hφ)
    j hj (NestedCapTimeSingleSource.source X U E m p c₀ hc₀ φ ψ j hi₀)
    (NestedCapTimeSingleSource.source X V E m p c₁ hc₁ φ ψ j hi₁) hz₀ hz₁ q
  exact h₀.trans (he.trans h₁.symm)

theorem retained_homology (q : ℕ) :
    (FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η₀ hη₀ hρr g₀ hT).homology q =
    (FirstInputRotationFullTime.retainedOperation α β R r hR hr p T h F B η₁ hη₁ hρr g₁ hT).homology q := by
  rw [FirstInputRotationFullTime.retainedOperation, FirstInputRotationFullTime.retainedOperation,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    bounded_homology α β R r hR hr p T h F B η₀ η₁ hη₀ hη₁ hρr g₀ g₁ hT q]

theorem endpoint_homology (s : _root_.unitInterval) (q : ℕ) :
    (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F B η₀ hη₀ hρr g₀ hT s).homology q =
    (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F B η₁ hη₁ hρr g₁ hT s).homology q := by
  rw [FirstInputRotationTimeEndpoints.endpoint, FirstInputRotationTimeEndpoints.endpoint,
    DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology,
    retained_homology α β R r hR hr p T h F B η₀ η₁ hη₀ hη₁ hρr g₀ g₁ hT q]

theorem joined_homology {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (s : _root_.unitInterval) (q : ℕ) :
    (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F B η₀ hη₀ hρr g₀ hT s).homology q =
    (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F B η₁ hη₁ hρr g₁ hT s).homology q := by
  rw [FirstInputRotationJoinedTime.joined, FirstInputRotationJoinedTime.joined,
    DegreeLoweringComposition.homology, DegreeLoweringComposition.homology,
    endpoint_homology α β R r hR hr p T h F B η₀ η₁ hη₀ hη₁ hρr g₀ g₁ hT s q]

end
end Finsler.RotationTimeCoverIndependence
