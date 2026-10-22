module

public import Finsler.Loop.CommonRegradedCapTime
public import Finsler.Loop.OriginalFirstHalfCutThenJoinTime

/-! The actual original geometric first-half time is independent of its
real cover scale and adequacy witness in the identical retained target.
The actual original cup-time source is fixed on the common small input. -/

@[expose] public section
namespace Finsler.GeometricTimeCoverIndependence

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJointSupportedCap
open Finsler.OriginalFirstHalfCupOrderCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {κ : ℝ} (hκ : 0 < κ) (hκR : κ < R) (F : ReversibleMetric (m + 1)) (B η₀ η₁ : ℝ)
  (hη₀ : 0 < η₀) (hη₁ : 0 < η₁) (hρr : ρ < r)
  (g₀ : ∀ v, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η₀ (((m + 1) + (m + p)) + 1)
    (properOrder α β R r hR hr h p T hκ v))
  (g₁ : ∀ v, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η₁ (((m + 1) + (m + p)) + 1)
    (properOrder α β R r hR hr h p T hκ v))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem cup_homology (v : Bool) (q : ℕ) :
    (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η₀ hη₀ hρr g₀ hT v).homology q =
    (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η₁ hη₁ hρr g₁ hT v).homology q := by
  let X := TopCat.of (P × Q)
  let U := OriginalFirstHalfJointCover.cover α β R r η₀ κ ρ
  let V := OriginalFirstHalfJointCover.cover α β R r η₁ κ ρ
  let E := chains (TopCat.of (bounded α β R r hR hr F B))
  let d := (m + 1) + (m + p)
  let c₀ := OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η₀ g₀ v hT
  let c₁ := OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η₁ g₁ v hT
  let C := inner α β δ
  let φ := originalOrder α β r hr h p T hκ v
  let hφ := original_inner_zero α β r hr h p T hκ v
  let j := push (source α β R r hR hr F B)
  let hj := source_mono α β R r hR hr F B
  let hs₀ := OriginalFirstHalfCupOrderBounded.cap_source α β R r hR hr h p T hκ F B η₀ g₀ v
  let hs₁ := OriginalFirstHalfCupOrderBounded.cap_source α β R r hR hr h p T hκ F B η₁ g₁ v
  have hz₀ : ∀ x : P × Q, ((0 : ClosedInterval), x) ∈ C :=
    fun x => (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le
  have hz₁ : ∀ x : P × Q, ((1 : ClosedInterval), x) ∈ C :=
    fun x => (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le
  let a₀ := RegradedSingleCapTime.operation X U (OriginalFirstHalfJointCover.cover_open α β R r η₀ κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η₀ hη₀ hκR hρr) E d (d + 1) rfl c₀ C φ hφ j hj hs₀ hz₀ hz₁
  let a₁ := RegradedSingleCapTime.operation X V (OriginalFirstHalfJointCover.cover_open α β R r η₁ κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η₁ hη₁ hκR hρr) E d (d + 1) rfl c₁ C φ hφ j hj hs₁ hz₀ hz₁
  have he := CommonRegradedCapTime.homology_eq X U V (OriginalFirstHalfJointCover.cover_open α β R r η₀ κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η₀ hη₀ hκR hρr) (OriginalFirstHalfJointCover.cover_open α β R r η₁ κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η₁ hη₁ hκR hρr) E d (d + 1) rfl c₀ c₁ C φ hφ j hj hs₀ hs₁ hz₀ hz₁ q
  have he₀ : (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η₀ hη₀ hρr g₀ hT v).homology q = a₀.homology q := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro k
    rw [OriginalFirstHalfCupOrderTimeHomology.component_normal]
    rfl
  have he₁ : (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η₁ hη₁ hρr g₁ hT v).homology q = a₁.homology q := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro k
    rw [OriginalFirstHalfCupOrderTimeHomology.component_normal]
    rfl
  exact he₀.trans (he.trans he₁.symm)

theorem geometric_homology (q : ℕ) :
    (OriginalFirstHalfCutThenJoinTime.operation α β R r η₀ hR hr hκ hκR hη₀ h hρr p T F B g₀ hT).homology q =
    (OriginalFirstHalfCutThenJoinTime.operation α β R r η₁ hR hr hκ hκR hη₁ h hρr p T F B g₁ hT).homology q := by
  rw [OriginalFirstHalfCutThenJoinTime.homology_eq, OriginalFirstHalfCutThenJoinTime.homology_eq,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    cup_homology α β R r hR hr h p T hκ hκR F B η₀ η₁ hη₀ hη₁ hρr g₀ g₁ hT true q]

end
end Finsler.GeometricTimeCoverIndependence
