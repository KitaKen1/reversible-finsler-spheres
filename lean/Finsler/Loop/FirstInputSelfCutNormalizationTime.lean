module

public import Finsler.Loop.FirstInputSelfCutNormalizationRetraction
public import Finsler.Loop.TimePrismCapCoboundaryAllDegrees
public import Finsler.Topology.DegreeLoweringExact

/-! The genuine raw and normalized single-input cut-time operations
agree in the identical proper-cut small target. The explicit boundary
uses the actual primitive, literal local error and both endpoint collars. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutNormalizationTime

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open Finsler.FirstInputSelfCutNormalizationRetraction

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
  (σ : ℝ) (hσ : 0 < σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))

def timePrimitive (q : ℕ) :=
  AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
    retractedPrimitive α r hr κ h p T σ hσ firstIndex hfirst (q + 1)

def timeBoundary (q : ℕ) :=
  AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
    eqToHom (congrArg (chains (ambient α)).X
      (show ((m + p) + q) + 1 = ((m + p) + 1) + q by omega)) ≫
    retractedBoundary α r hr κ h p T hT σ hσ firstIndex hfirst q

theorem component_difference (q : ℕ) :
    (FirstInputSelfCutTime.operation α r hr κ h p T hT σ hσ firstIndex hfirst true).component q -
      (FirstInputSelfCutTime.operation α r hr κ h p T hT σ hσ firstIndex hfirst false).component q =
    timeBoundary α r hr κ h p T hT σ hσ firstIndex hfirst q := by
  rw [FirstInputSelfCutTime.component_normal, FirstInputSelfCutTime.component_normal]
  simp only [timeBoundary, boundary_normal, Category.assoc]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  simp only [Preadditive.comp_sub]
  rfl

theorem cycle_boundary {Z : ModuleCat.{0} (ZMod 2)} (q : ℕ)
    (z : Z ⟶ (chains (TopCat.of P)).X ((m + p) + q))
    (hz : z ≫ (chains (TopCat.of P)).d ((m + p) + q) (((m + p) + q) - 1) = 0) :
    z ≫ timeBoundary α r hr κ h p T hT σ hσ firstIndex hfirst q =
    -(z ≫ timePrimitive α r hr κ h p T σ hσ firstIndex hfirst q) ≫
      (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).d (q + 1) q :=
  TimePrismCapCoboundaryAllDegrees.cycle_boundary
    ((AnnularTimeTrim.cylinder (TopCat.of P)).toSSet.chainComplexMap coeff) ((m + p) + q) q
    (retractedPrimitive α r hr κ h p T σ hσ firstIndex hfirst q)
    (retractedPrimitive α r hr κ h p T σ hσ firstIndex hfirst (q + 1))
    (eqToHom (congrArg (chains (ambient α)).X
      (show ((m + p) + q) + 1 = ((m + p) + 1) + q by omega)) ≫
      retractedBoundary α r hr κ h p T hT σ hσ firstIndex hfirst q)
    (retracted_boundary α r hr κ h p T hT σ hσ firstIndex hfirst q)
    (endpoint_zero α r hr κ h p T σ hσ firstIndex hfirst 0 (Or.inl rfl) q)
    (endpoint_zero α r hr κ h p T σ hσ firstIndex hfirst 1 (Or.inr rfl) q) z hz

theorem homology_eq (q : ℕ) :
    (FirstInputSelfCutTime.operation α r hr κ h p T hT σ hσ firstIndex hfirst true).homology q =
      (FirstInputSelfCutTime.operation α r hr κ h p T hT σ hσ firstIndex hfirst false).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (-timePrimitive α r hr κ h p T σ hσ firstIndex hfirst q)
  rw [component_difference]
  have hh := cycle_boundary α r hr κ h p T hT σ hσ firstIndex hfirst q
    ((chains (TopCat.of P)).iCycles ((m + p) + q)) ((chains (TopCat.of P)).iCycles_d _ _)
  simpa only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using hh

theorem sectioned_homology_eq (q : ℕ) :
    (FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst true).homology q =
      (FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst false).homology q := by
  rw [FirstInputSelfCutTime.sectioned_homology, FirstInputSelfCutTime.sectioned_homology,
    homology_eq α r hr κ h p T hT σ hσ firstIndex hfirst q]

end
end Finsler.FirstInputSelfCutNormalizationTime
