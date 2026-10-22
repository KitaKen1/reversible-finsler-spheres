module

public import Finsler.Loop.CompactFixedScaleLengthProduct
public import Finsler.Loop.CanonicalAfterLengthProduct

/-! Actual native full after actual spatial join equals canonical
D_T after the GENUINE strict-length product in the identical coupled
short target. All real individual bounds and output degree zero remain. -/

@[expose] public section
namespace Finsler.CompactJoinCanonicalAfterProduct
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge
open Finsler.FarNormalizedDiagonalCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (F : ReversibleMetric (m + 1))
  {a b A L ε : ℝ} (hab : a + b < A) (hε : 0 < ε)
  (hα : ∀ x, SobolevLength.length F (α x) < a) (hβ : ∀ y, SobolevLength.length F (β y) < b)
  (R : ℝ) (hR : R ≤ 1 / 2) {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R)
  (hΓ : ∀ z, SobolevLength.length F (JoinedNativeCanonicalTime.joinedFamily α β R hR z) < A + 2 * ε)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0)
  (full : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (chains (lengthSpace F (A - L + 5 * ε))) (m + p))
  (hfull : ∀ q, full.homology q =
    (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
      (push (CompactInputShortMaps.family (JoinedNativeCanonicalTime.joinedFamily α β R hR) F (A + 2 * ε) hΓ))).post
      (CanonicalAfterLengthProduct.outputTransport F (A := A) (L := L) (ε := ε))).homology q)

include hfull in
theorem homology_eq (hm : 1 ≤ m) (k : ℕ) :
    (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (dim_pos m) hκ hκR) full).homology k =
    ((CanonicalAfterLengthProduct.operation F hab hε p T hT hshort).pre
      (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ))).homology k := by
  have hs := CompactFixedScaleLengthProduct.operation_homology α β F a b hα hβ hε R hR (A + 2 * ε)
    (CanonicalAfterLengthProduct.input_budget hab hε) hΓ hκ hκR hm ((m + p) + k)
  rw [CanonicalAfterLengthProduct.family_homology]
  simp only [DegreeLoweringHomology.Map.post_homology, DegreeLoweringComposition.homology,
    hfull k, DegreeLoweringHomology.Map.pre_homology, Category.assoc]
  have hs' := hs
  rw [DegreeLoweringHomology.Map.post_homology] at hs'
  rw [← Category.assoc
    ((CompactJoinCapLocalization.unrefined α β (dim_pos m) hκ hκR).homology ((m + p) + k)), hs']
  rw [DegreeLoweringHomology.Map.pre_homology]
  simp only [Category.assoc]

end
end Finsler.CompactJoinCanonicalAfterProduct
