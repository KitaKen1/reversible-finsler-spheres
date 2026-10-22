module

public import Finsler.Loop.FilteredGlobalSelfCut
public import Finsler.Loop.GlobalTimeCupCohomology

/-! Restrict the independently constructed GLOBAL absolute time cup
to the actual strict length sublevel: its class is precisely the
independently geometric canonical filtered cochain. Genuine canonical
cut pairing follows, using Lean Pool's natural Kronecker isomorphism. -/

@[expose] public section
namespace Finsler.GlobalFilteredTimeCup
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ} (hε : 0 < ε)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (q : ℕ) (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
  (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0)

theorem cohomology :
    (cohPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F a)) ((m + p) + q)).hom
      (GlobalTimeCupCohomology.product m (half_pos (SelfCutLengthControl.radius_spec F hε).1)
        (half_lt_self (SelfCutLengthControl.radius_spec F hε).1)
        (SelfCutLengthControl.radius_spec F hε).2.1 p q (cocycleClass _ p T hT) (cocycleClass _ q B hB)) =
    cocycleClass _ _ (FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B)
      (FilteredCanonicalCutPairing.closed m p F hε T hT hshort q B hB) := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  rw [kroneckerMap_naturality_apply]
  change (kroneckerMap (TopCat.of (SphereLoop (m + 1))) ((m + p) + q)).hom
    (GlobalTimeCupCohomology.product m (half_pos (SelfCutLengthControl.radius_spec F hε).1)
      (half_lt_self (SelfCutLengthControl.radius_spec F hε).1)
      (SelfCutLengthControl.radius_spec F hε).2.1 p q (cocycleClass _ p T hT) (cocycleClass _ q B hB))
    ((HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F a))) ((m + p) + q)).hom z) = _
  rw [GlobalTimeCupCohomology.pairing, FilteredCanonicalCutPairing.pairing m p F hε T hT hshort q B hB z]
  have h := ConcreteCategory.congr_hom (FilteredGlobalSelfCut.canonical_homology m p F hε T hT hshort q) z
  rw [h]
  rfl

theorem pairing (z : PoolCap.homology (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)) :
    (kroneckerMap _ ((m + p) + q)).hom
      ((cohPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F a)) ((m + p) + q)).hom
        (GlobalTimeCupCohomology.product m (half_pos (SelfCutLengthControl.radius_spec F hε).1)
          (half_lt_self (SelfCutLengthControl.radius_spec F hε).1)
          (SelfCutLengthControl.radius_spec F hε).2.1 p q (cocycleClass _ p T hT) (cocycleClass _ q B hB))) z =
    (kroneckerMap (TopCat.of (SphereLoop (m + 1))) q).hom (cocycleClass _ q B hB)
      ((PoolCap.push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε))) q).hom
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).homology q).hom z)) := by
  rw [cohomology m p F hε T hT hshort q B hB]
  exact FilteredCanonicalCutPairing.canonical_pairing m p F hε T hT hshort q B hB z

end
end Finsler.GlobalFilteredTimeCup
