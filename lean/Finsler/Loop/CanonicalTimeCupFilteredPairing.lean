module

public import Finsler.Loop.CanonicalGlobalTimeCup
public import Finsler.Loop.RelativeCanonicalTimeCupPairing

/-! The single metric/epsilon-independent actual time-cup operation
pairs with the ORIGINAL canonical filtered D_T for EVERY metric and
positive epsilon. Its high-degree relative pairing uses the ACTUAL
fullPair singular homology quotient, not an assumed pairing field. -/

@[expose] public section
namespace Finsler.CanonicalTimeCupFilteredPairing
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

variable (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ} (hε : 0 < ε)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
  (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L)) p T = 0)
  (q : ℕ) (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
  (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0)

include hm

theorem cohomology :
    (cohPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F a)) ((m + p) + q)).hom
      (CanonicalGlobalTimeCup.product m p q (cocycleClass _ p T hT) (cocycleClass _ q B hB)) =
    cocycleClass _ _ (FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B)
      (FilteredCanonicalCutPairing.closed m p F hε T hT hshort q B hB) := by
  rw [← CanonicalGlobalTimeCup.product_compare m hm p q (half_pos (SelfCutLengthControl.radius_spec F hε).1)
    (half_lt_self (SelfCutLengthControl.radius_spec F hε).1) (SelfCutLengthControl.radius_spec F hε).2.1]
  exact GlobalFilteredTimeCup.cohomology m p F hε T hT hshort q B hB

theorem pairing (z : PoolCap.homology (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)) :
    (kroneckerMap _ ((m + p) + q)).hom
      ((cohPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F a)) ((m + p) + q)).hom
        (CanonicalGlobalTimeCup.product m p q (cocycleClass _ p T hT) (cocycleClass _ q B hB))) z =
    (kroneckerMap (Loops (m + 1)) q).hom (cocycleClass _ q B hB)
      ((PoolCap.push (SupportedCap.subspaceMap (Loops (m + 1))
        (SelfCutOscillation.short F (a - L + 3 * ε))) q).hom
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).homology q).hom z)) := by
  rw [cohomology m hm p F hε T hT hshort q B hB]
  exact FilteredCanonicalCutPairing.canonical_pairing m p F hε T hT hshort q B hB z

theorem relative_pairing (hk : (m + 1) + 1 < (m + p) + q)
    (z : PoolCap.homology (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)) :
    RelativeKronecker.comparison (fullPair (m + 1)) ((m + p) + q)
      (CanonicalGlobalTimeCup.relative m p q hk (cocycleClass _ p T hT) (cocycleClass _ q B hB))
      (ConstantRelativePairing.homologyToRelative (m + 1) ((m + p) + q)
        ((PoolCap.push (SupportedCap.subspaceMap (Loops (m + 1))
          (SelfCutOscillation.short F a)) ((m + p) + q)).hom z)) =
    (kroneckerMap (Loops (m + 1)) q).hom (cocycleClass _ q B hB)
      ((PoolCap.push (SupportedCap.subspaceMap (Loops (m + 1))
        (SelfCutOscillation.short F (a - L + 3 * ε))) q).hom
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).homology q).hom z)) := by
  rw [← CanonicalGlobalTimeCup.relative_compare m hm p q (half_pos (SelfCutLengthControl.radius_spec F hε).1)
    (half_lt_self (SelfCutLengthControl.radius_spec F hε).1) (SelfCutLengthControl.radius_spec F hε).2.1 hk]
  exact RelativeCanonicalTimeCupPairing.pairing m p F hε T hT hshort q hk B hB z

end
end Finsler.CanonicalTimeCupFilteredPairing
