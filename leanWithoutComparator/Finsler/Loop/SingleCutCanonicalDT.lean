module

public import Finsler.Loop.SingleCutCanonicalFullTime
public import Finsler.Loop.CanonicalCutRadiusData
public import Finsler.Loop.RegradedTimeCoverComparison
public import Finsler.Loop.SingleCutBoundedCanonicalThomTime
public import Finsler.Loop.SingleCutCanonicalThomEndpoints
public import Finsler.Loop.RegradedSingleCapTime

/-! Identify the constructed raw and normalized annular family time
maps with the actual specified canonical D_T after the real short input
map, in the literal individual short output target. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalDT

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

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


variable (R : ℝ) (hrR : r < R) (hR : R ≤ 1) (hρr : ρ < r)

include hρr in
theorem retained_canonical_DT (hRe : R = SelfCutLengthControl.radius F hε)
    (hρe : ρ = R / 2) (hm : 1 ≤ m) (v : Bool) (q : ℕ) :
    (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA v).homology q =
    ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshortT).pre
      (push (CompactInputShortMaps.family α F a hA))).homology q := by
  subst R
  subst ρ
  have hrR : r < SelfCutLengthControl.radius F hε := hradius
  have hR : SelfCutLengthControl.radius F hε ≤ 1 := (SelfCutLengthControl.radius_spec F hε).2.1
  have hρ2 : SelfCutLengthControl.radius F hε / 2 ≤ 2 := by
    have hb := (SelfCutLengthControl.radius_spec F hε).2.1
    linarith
  cases v
  · have hh := SingleCutCanonicalFullTime.raw_canonical_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA
      (SelfCutLengthControl.radius F hε) hrR hR hρr le_rfl hm hρ2 q
    simpa only [SingleCutCanonicalTwoStage.familyOperation, FilteredPrismSelfCut.canonicalOperation] using hh
  · have hh := SingleCutCanonicalFullTime.normalized_canonical_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA
      (SelfCutLengthControl.radius F hε) hrR hR hρr le_rfl hm hρ2 q
    simpa only [SingleCutCanonicalTwoStage.familyOperation, FilteredPrismSelfCut.canonicalOperation] using hh

end
end Finsler.SingleCutCanonicalDT
