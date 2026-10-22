module

public import Finsler.Loop.OriginalFirstHalfNormalizationCup
public import Finsler.Loop.OriginalFirstHalfJointCochainZero
public import Finsler.Topology.SupportedCapCochain
import all Finsler.Loop.OriginalFirstHalfNormalizationCup

/-! Remove the literal original-cylinder normalization error on the
actual joint cover. No global closure of gamma or its zero extension
is assumed. The new cup cap is locally closed on this same cover. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizationLocalError

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)
  (η : ℝ) (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hR hT in
theorem error_small_cap_zero (q : ℕ) :
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (OriginalFirstHalfNormalizationCup.error α β r hr h p T hκ) = 0 :=
  OriginalFirstHalfJointCochainZero.small_cap_zero α β R r η κ ρ _ _
    (OriginalFirstHalfNormalizationCup.error_join_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.error_cut_far_zero α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.error_source_zero α β r hr h p T hκ R hR hT) q

include hR hT in
theorem boundary_difference (q : ℕ) :
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p))
          (OriginalFirstHalfNormalizationCup.primitive α β r hr h p T hκ)) =
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) -
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (OriginalFirstHalfCupOrderCochains.originalOrder α β r hr h p T hκ true) := by
  have he := error_small_cap_zero α β R r hR hr h p T hκ η hT q
  rw [OriginalFirstHalfNormalizationCup.error, SupportedCapCochain.absolute_sub,
    SupportedCapCochain.absolute_sub, Preadditive.comp_sub, Preadditive.comp_sub] at he
  exact sub_eq_zero.mp he

include hR hT in
theorem order_boundary_small_zero (q : ℕ) :
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f (((((m + 1) + (m + p)) + 1) + 1) + q) ≫
      absoluteChain (ambient α β) ((((m + 1) + (m + p)) + 1) + 1) q (((((m + 1) + (m + p)) + 1) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1)
          (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ)) = 0 := by
  apply OriginalFirstHalfJointCochainZero.small_cap_zero α β R r η κ ρ _ _ _ _ _ q
  · rw [OriginalFirstHalfNormalizationCup.coboundary_pullback,
      OriginalFirstHalfNormalizationCup.order_join_far_zero]
    exact map_zero _
  · rw [OriginalFirstHalfNormalizationCup.coboundary_pullback,
      OriginalFirstHalfNormalizationCup.order_cut_far_zero]
    exact map_zero _
  · exact OriginalFirstHalfNormalizationCup.source_order_boundary_zero α β r hr h p T hκ R hR hT

end
end Finsler.OriginalFirstHalfNormalizationLocalError
