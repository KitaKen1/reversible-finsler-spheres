module

public import Finsler.Loop.FilteredSelfCutSupportRadius
public import Finsler.Loop.SingleCutCanonicalDT

/-! The actual retained raw/normalized annular time equals the fixed
canonical D_T for every positive support radius below the proper cut
radius. This includes the smaller native-compatible support radii. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalAnyRadius

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

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


theorem retained_canonical_DT (hρr : ρ < r) (hm : 1 ≤ m) (v : Bool) (q : ℕ) :
    (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA v).homology q =
    ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshortT).pre
      (push (CompactInputShortMaps.family α F a hA))).homology q := by
  have hS := (SelfCutLengthControl.radius_spec F hε).2.1
  have hρ2 : ρ ≤ 2 := by linarith [hρr, hradius]
  have hh : (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA v).homology q =
    (SingleCutCanonicalTwoStage.familyOperation α F a (SelfCutLengthControl.radius F hε) hA hS ε h hε le_rfl
      L p T hT hshortT (hρr.trans hradius)).homology q := by
    cases v
    · exact SingleCutCanonicalFullTime.raw_canonical_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
        firstIndex hfirst hshortT hA (SelfCutLengthControl.radius F hε) hradius hS hρr le_rfl hm hρ2 q
    · exact SingleCutCanonicalFullTime.normalized_canonical_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
        firstIndex hfirst hshortT hA (SelfCutLengthControl.radius F hε) hradius hS hρr le_rfl hm hρ2 q
  rw [hh, SingleCutCanonicalTwoStage.familyOperation, DegreeLoweringHomology.Map.pre_homology,
    FilteredSelfCutSupportRadius.canonical m p F hm hε T hT hshortT (h.1.trans h.2.2) (hρr.trans hradius) q,
    DegreeLoweringHomology.Map.pre_homology]

theorem native_radii {n : ℕ} (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    let S := SelfCutLengthControl.radius F hε
    (0 < S / 32 ∧ S / 32 ≤ 1 ∧ S / 32 < S / 16) ∧
    4 * (S / 16) < 3 * S / 4 ∧ 3 * S / 4 < 1 ∧ 3 * S / 4 < S := by
  dsimp only
  have hp := (SelfCutLengthControl.radius_spec F hε).1
  have hS := (SelfCutLengthControl.radius_spec F hε).2.1
  refine ⟨⟨by linarith, by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩

end
end Finsler.SingleCutCanonicalAnyRadius
