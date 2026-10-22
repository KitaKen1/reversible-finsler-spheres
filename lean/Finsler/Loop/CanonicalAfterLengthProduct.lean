module

public import Finsler.Loop.OriginalLengthProductBudget
public import Finsler.Loop.DegreeLoweringCompositionInput
public import Finsler.Topology.FilteredPrismSelfCut

/-! The actual genuine strict-length product followed by the fixed
canonical self-cut D_T, with exact transport to the coupled short bound.
This is the specified product operation, not a replacement native map. -/

@[expose] public section
namespace Finsler.CanonicalAfterLengthProduct
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable {m : ℕ} (F : ReversibleMetric (m + 1)) {a b A L ε : ℝ} (hab : a + b < A) (hε : 0 < ε)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0)

include hab hε in
theorem input_budget : a + (b + ε) ≤ A + 2 * ε := by linarith

def outputTransport := eqToHom (congrArg (fun c : ℝ => chains (TopCat.of (SelfCutOscillation.short F c)))
  (show (A + 2 * ε) - L + 3 * ε = A - L + 5 * ε by ring))

def operation := (DegreeLoweringComposition.compose
  (OriginalLengthProductBudget.operation F (input_budget hab hε) (by omega) hε)
  (FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort)).post
  (outputTransport F (A := A) (L := L) (ε := ε))

variable {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
  (hα : ∀ x, SobolevLength.length F (α x) < a) (hβ : ∀ y, SobolevLength.length F (β y) < b)


theorem family_homology (k : ℕ) :
    ((operation F hab hε p T hT hshort).pre (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ))).homology k =
    ((DegreeLoweringComposition.compose
      ((OriginalLengthProductBudget.operation F (input_budget hab hε) (by omega) hε).pre
        (push (StrictLengthProductFamilies.pairInput α β F a b hα hβ)))
      (FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort)).post
        (outputTransport F (A := A) (L := L) (ε := ε))).homology k := by
  rw [DegreeLoweringHomology.Map.post_homology,
    DegreeLoweringCompositionInput.pre_homology, DegreeLoweringHomology.Map.pre_homology,
    operation, DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.post_homology,
    Category.assoc]

end
end Finsler.CanonicalAfterLengthProduct
