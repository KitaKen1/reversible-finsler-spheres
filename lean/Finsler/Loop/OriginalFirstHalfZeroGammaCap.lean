module

public import Finsler.Loop.OriginalFirstHalfZeroGammaCochains
public import Finsler.Loop.OriginalFirstHalfZeroSupportedCap
public import Finsler.Loop.LiftedCapCochainBoundary

/-! The real closed bounded gamma cap on the near-pair zero
cylinder, before taking the spatial join cap or the time prism. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroGammaCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfZeroCover Finsler.OriginalFirstHalfZeroGammaCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))

def component (q : ℕ) : (small (space α β R) (cover α β R r η ρ)).X (((m + 1) + p) + q) ⟶
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))).X q :=
  OriginalFirstHalfZeroSupportedCap.component α β R r hR hr F B η ρ ((m + 1) + p)
    (gamma α β R r hr h p T) (FirstInputRotationCupOne.gamma α β R r hR hr h p T)
    (far_zero α β R r hr h p T η) (source_restriction α β R r hR hr h p T) good q

theorem component_source (q : ℕ) :
    component α β R r hR hr h p T F B η good q ≫
      (push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B)).f q =
    (inclusion (space α β R) (cover α β R r η ρ)).f (((m + 1) + p) + q) ≫
      absoluteChain (space α β R) ((m + 1) + p) q (((m + 1) + p) + q) rfl (gamma α β R r hr h p T) :=
  OriginalFirstHalfZeroSupportedCap.component_source α β R r hR hr F B η ρ _ _ _ _ _ _ q

theorem component_comm
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    component α β R r hR hr h p T F B η good (q + 1) ≫
      (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))).d (q + 1) q =
    (small (space α β R) (cover α β R r η ρ)).d (((m + 1) + p) + (q + 1)) (((m + 1) + p) + q) ≫
      component α β R r hR hr h p T F B η good q := by
  have hb := LiftedCapCochainBoundary.boundary (cover α β R r η ρ)
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B)))
    (push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B))
    (OriginalFirstHalfZeroSupportedCap.sourceBounded_mono α β R r hR hr F B)
    ((m + 1) + p) (gamma α β R r hr h p T) (component α β R r hR hr h p T F B η good) (fun _ => 0)
    (component_source α β R r hR hr h p T F B η good)
    (fun q => by rw [zero_comp, boundary_small_zero α β R r hR hr h p T η hT q]) q
  simpa only [comp_zero, sub_zero] using hb

def operation (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    DegreeLoweringHomology.Map (small (space α β R) (cover α β R r η ρ))
      (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) ((m + 1) + p) where
  component := component α β R r hR hr h p T F B η good
  comm := component_comm α β R r hR hr h p T F B η good hT

theorem exists_uniform [CompactSpace P] [CompactSpace Q] {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < u →
      ∃ η > 0, η ≤ b ∧ ∀ (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (SelfCutOscillation.short F L)) p T = 0 →
        (∀ z : CompactNearJoinParameters.tube α β R,
          SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A) →
        ∀ {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ),
        FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η ((m + 1) + p)
          (FirstInputRotationCupOne.gamma α β R r hR hr h p T) := by
  obtain ⟨u, hu, hu1, hscale⟩ := FirstInputRotationSupportedCap.exists_uniform α β r hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro p L A T hshort hA δ ρ h
  exact had _ L A _ (TestedCupOneSupport.gamma_zero F (FirstInputRotationCochains.testedMap α β R r hR hr) L
    (m + 1) p (FirstInputRotationCochains.thom α β R r hR hr (by omega) h) T hshort) hA

end
end Finsler.OriginalFirstHalfZeroGammaCap
