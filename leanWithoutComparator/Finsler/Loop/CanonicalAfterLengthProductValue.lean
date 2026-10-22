module

public import Finsler.Loop.DegreeLoweringCompositionCross
public import Finsler.Loop.CanonicalAfterLengthProduct

/-! Evaluate the specified canonical-after-genuine-product operation
on the actual homology cross, with its native input cast and literal
output-length equality transport retained. -/

@[expose] public section
namespace Finsler.CanonicalAfterLengthProductValue
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

theorem value {m : ℕ} (F : ReversibleMetric (m + 1)) {a b A L ε : ℝ}
    (hab : a + b < A) (hε : 0 < ε) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0)
    (i j k : ℕ) (h : i + j = ((m + 1) + (m + p)) + k)
    (x : PoolCap.homology (lengthSpace F a) i) (y : PoolCap.homology (lengthSpace F b) j) :
    ((CanonicalAfterLengthProduct.operation F hab hε p T hT hshort).homology k).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j
        (((m + 1) + (m + p)) + k) h x y) =
    (homologyMap (CanonicalAfterLengthProduct.outputTransport F (A := A) (L := L) (ε := ε)) k).hom
      (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).homology k).hom
        (((OriginalLengthProductBudget.operation F (CanonicalAfterLengthProduct.input_budget hab hε)
          (by omega) hε).homology ((m + p) + k)).hom
          (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j
            ((m + 1) + ((m + p) + k)) (by omega) x y))) := by
  rw [CanonicalAfterLengthProduct.operation, DegreeLoweringHomology.Map.post_homology]
  change (homologyMap (CanonicalAfterLengthProduct.outputTransport F (A := A) (L := L) (ε := ε)) k).hom
      (((DegreeLoweringComposition.compose
        (OriginalLengthProductBudget.operation F (CanonicalAfterLengthProduct.input_budget hab hε) (by omega) hε)
        (FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort)).homology k).hom
          (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j
            (((m + 1) + (m + p)) + k) h x y)) = _
  rw [DegreeLoweringCompositionCross.value]

end
end Finsler.CanonicalAfterLengthProductValue
