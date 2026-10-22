module

public import Finsler.Loop.FirstInputSelfCutBoundedNormalizationRetraction
public import Finsler.Loop.TimePrismCapCoboundaryAllDegrees
public import Finsler.Topology.DegreeLoweringExact

/-! The genuine raw and normalized single-input cut-time operations
agree in the identical individually bounded small target and after the
actual retained map into length<a-L+3epsilon, in every degree. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedNormalizationTime

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open Finsler.FirstInputSelfCutBoundedNormalizationRetraction

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
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)


def timePrimitive (q : ℕ) :=
  AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
    retractedPrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA (q + 1)

def timeBoundary (q : ℕ) :=
  AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
    eqToHom (congrArg (chains (ambient α)).X
      (show ((m + p) + q) + 1 = ((m + p) + 1) + q by omega)) ≫
    retractedBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q

theorem component_difference (q : ℕ) :
    (FirstInputSelfCutBoundedTime.operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA true).component q -
      (FirstInputSelfCutBoundedTime.operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA false).component q =
    timeBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q := by
  rw [FirstInputSelfCutBoundedTime.component_normal, FirstInputSelfCutBoundedTime.component_normal]
  simp only [timeBoundary, boundary_normal, Category.assoc]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  simp only [Preadditive.comp_sub]

theorem cycle_boundary {Z : ModuleCat.{0} (ZMod 2)} (q : ℕ)
    (z : Z ⟶ (chains (TopCat.of P)).X ((m + p) + q))
    (hz : z ≫ (chains (TopCat.of P)).d ((m + p) + q) (((m + p) + q) - 1) = 0) :
    z ≫ timeBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q =
    -(z ≫ timePrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q) ≫
      (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q :=
  TimePrismCapCoboundaryAllDegrees.cycle_boundary
    ((AnnularTimeTrim.cylinder (TopCat.of P)).toSSet.chainComplexMap coeff) ((m + p) + q) q
    (retractedPrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q)
    (retractedPrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA (q + 1))
    (eqToHom (congrArg (chains (ambient α)).X
      (show ((m + p) + q) + 1 = ((m + p) + 1) + q by omega)) ≫
      retractedBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q)
    (retracted_boundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q)
    (endpoint_zero α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA 0 (Or.inl rfl) q)
    (endpoint_zero α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA 1 (Or.inr rfl) q) z hz

theorem homology_eq (q : ℕ) :
    (FirstInputSelfCutBoundedTime.operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA true).homology q =
      (FirstInputSelfCutBoundedTime.operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA false).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (-timePrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q)
  rw [component_difference]
  have hh := cycle_boundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q
    ((chains (TopCat.of P)).iCycles ((m + p) + q)) ((chains (TopCat.of P)).iCycles_d _ _)
  simpa only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using hh

theorem sectioned_homology_eq (q : ℕ) :
    (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA true).homology q =
      (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA false).homology q := by
  rw [FirstInputSelfCutBoundedTime.sectioned, FirstInputSelfCutBoundedTime.sectioned,
    DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology,
    homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q]

theorem retained_homology_eq (q : ℕ) :
    (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA true).homology q =
      (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA false).homology q := by
  rw [FirstInputSelfCutBoundedTime.retained, FirstInputSelfCutBoundedTime.retained,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q]

end
end Finsler.FirstInputSelfCutBoundedNormalizationTime
