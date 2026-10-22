module

public import Finsler.Loop.FirstInputSelfCutNormalizationError
public import Finsler.Loop.FirstInputSelfCutTime

/-! The real single-input normalization primitive cap and its full
boundary identity in the same proper-cut small complex. The boundary
cap is the actual normalized/raw difference after local error removal. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutNormalizationCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def primitiveCap (q : ℕ) := FirstInputSelfCutCarrierCap.component α r hr κ ρ (m + p)
  (primitive α r hr h p T) (primitive_far_zero α r hr h p T) q

def boundaryCap (q : ℕ) :=
  eqToHom (congrArg (small (ambient α) (cover α r hr κ ρ)).X
    (show ((m + p) + 1) + q = ((m + 1) + p) + q by omega)) ≫
  ((FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT).component q -
    (FirstInputSelfCutOperations.rawOperation α r hr κ h p T hT).component q)

theorem primitive_source (q : ℕ) :
    primitiveCap α r hr κ h p T q ≫ (FirstInputSelfCutTime.sourceMap α r hr κ).f q =
    (inclusion (ambient α) (cover α r hr κ ρ)).f ((m + p) + q) ≫
      absoluteChain (ambient α) (m + p) q ((m + p) + q) rfl (primitive α r hr h p T) := by
  simpa only [primitiveCap, FirstInputSelfCutTime.sourceMap, HomologicalComplex.comp_f, Category.assoc] using
    FirstInputSelfCutCarrierCap.component_source α r hr κ ρ (m + p)
      (primitive α r hr h p T) (primitive_far_zero α r hr h p T) q

theorem boundary_source (q : ℕ) :
    boundaryCap α r hr κ h p T hT q ≫ (FirstInputSelfCutTime.sourceMap α r hr κ).f q =
    (inclusion (ambient α) (cover α r hr κ ρ)).f (((m + p) + 1) + q) ≫
      absoluteChain (ambient α) ((m + p) + 1) q (((m + p) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α) (m + p) (primitive α r hr h p T)) := by
  have he := FirstInputSelfCutNormalizationError.error_small_cap_zero α r hr h p T hT κ q
  rw [FirstInputSelfCutNormalizationError.error, SupportedCapCochain.absolute_sub, Preadditive.comp_sub] at he
  have hh := sub_eq_zero.mp he
  rw [FirstInputSelfCutNormalizationError.difference, CochainInputRegrade.small_cap] at hh
  have hb :
      ((FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT).component q -
        (FirstInputSelfCutOperations.rawOperation α r hr κ h p T hT).component q) ≫
          (FirstInputSelfCutTime.sourceMap α r hr κ).f q =
      (inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + q) ≫
        absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl
          (normalized α r hr h p T - raw α r hr h p T) := by
    simp only [Preadditive.sub_comp, FirstInputSelfCutTime.sourceMap, HomologicalComplex.comp_f, Category.assoc]
    rw [FirstInputSelfCutOperations.normalized_source, FirstInputSelfCutOperations.raw_source,
      SupportedCapCochain.absolute_sub, Preadditive.comp_sub]
  dsimp only [boundaryCap]
  rw [Category.assoc, hb]
  exact hh.symm

theorem boundary (q : ℕ) :
    primitiveCap α r hr κ h p T (q + 1) ≫
      (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).d (q + 1) q =
    (small (ambient α) (cover α r hr κ ρ)).d ((m + p) + (q + 1)) ((m + p) + q) ≫
      primitiveCap α r hr κ h p T q -
    eqToHom (congrArg (small (ambient α) (cover α r hr κ ρ)).X
      (show (m + p) + (q + 1) = ((m + p) + 1) + q by omega)) ≫ boundaryCap α r hr κ h p T hT q :=
  LiftedCapCochainBoundary.boundary (cover α r hr κ ρ)
    (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ))
    (FirstInputSelfCutTime.sourceMap α r hr κ) (FirstInputSelfCutTime.sourceMap_mono α r hr κ)
    (m + p) (primitive α r hr h p T) (primitiveCap α r hr κ h p T)
    (boundaryCap α r hr κ h p T hT) (primitive_source α r hr κ h p T)
    (boundary_source α r hr κ h p T hT) q

end
end Finsler.FirstInputSelfCutNormalizationCap
