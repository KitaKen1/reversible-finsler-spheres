module

public import Finsler.Loop.FirstInputSelfCutCarrierCap
import all Finsler.Loop.OriginalFirstHalfCutGammaJoinCap

/-! Genuine raw and normalized single-input cut caps into the actual
proper-cut output-join carriers. Local proper closure supplies their
chain-map identities, without closure of the ambient zero extension. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutOperations

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hT in
theorem source_boundary_raw :
    cochainPullback (source α r) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α) ((m + 1) + p) (raw α r hr h p T)) = 0 := by
  rw [OriginalFirstHalfCutGammaJoinCap.coboundary_pullback, source_raw]
  exact OriginalFirstHalfCutNormalizedFactors.cutGamma_closed α r hr h p T hT

include hT in
theorem source_boundary_normalized :
    cochainPullback (source α r) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α) ((m + 1) + p) (normalized α r hr h p T)) = 0 := by
  rw [OriginalFirstHalfCutGammaJoinCap.coboundary_pullback, source_normalized]
  exact OriginalFirstHalfCutNormalizedFactors.normalized_closed α r hr h p T hT

def rawOperation := FirstInputSelfCutCarrierCap.operation α r hr κ ρ ((m + 1) + p)
  (raw α r hr h p T) (raw_far_zero α r hr h p T) (source_boundary_raw α r hr h p T hT)

def normalizedOperation := FirstInputSelfCutCarrierCap.operation α r hr κ ρ ((m + 1) + p)
  (normalized α r hr h p T) (normalized_far_zero α r hr h p T) (source_boundary_normalized α r hr h p T hT)

theorem raw_source (q : ℕ) :
    (rawOperation α r hr κ h p T hT).component q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).f q ≫
        (push (source α r)).f q =
    (inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl (raw α r hr h p T) :=
  FirstInputSelfCutCarrierCap.component_source α r hr κ ρ _ (raw α r hr h p T)
    (raw_far_zero α r hr h p T) q

theorem normalized_source (q : ℕ) :
    (normalizedOperation α r hr κ h p T hT).component q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).f q ≫
        (push (source α r)).f q =
    (inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl (normalized α r hr h p T) :=
  FirstInputSelfCutCarrierCap.component_source α r hr κ ρ _ (normalized α r hr h p T)
    (normalized_far_zero α r hr h p T) q

theorem normalized_degeneracies :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (ambient α))
      (normalized α r hr h p T) := SingularNormalization.normalize_degeneracies _ _ _

end
end Finsler.FirstInputSelfCutOperations
