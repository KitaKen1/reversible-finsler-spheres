module

public import Finsler.Loop.FilteredGeometricTimeCup

/-! The independently constructed geometric time cup pairs with the
ACTUAL canonical filtered D_T, followed by its actual ambient inclusion.
The equality uses real cochains and the Lean Pool Kronecker classifier. -/

@[expose] public section
namespace Finsler.FilteredCanonicalCutPairing
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

variable (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ} (hε : 0 < ε)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

def operation := (FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).post
  (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F (a - L + 3 * ε))))

theorem cochain_eq (q : ℕ)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q) :
    DegreeLoweringCochainPullback.cochain (operation m p F hε T hT hshort (a := a)) q B =
      FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B := by
  change ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).component q ≫
    (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F (a - L + 3 * ε)))).f q) ≫ B = _
  rw [Category.assoc, FilteredGeometricTimeCup.canonical_dual]

include hT hshort in
theorem closed (q : ℕ)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)
      (FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B) = 0 := by
  have h := DegreeLoweringCochainPullback.closed (operation m p F hε T hT hshort (a := a)) q B hB
  simpa only [cochain_eq] using h

theorem pairing (q : ℕ)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0)
    (z : PoolCap.homology (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)) :
    (kroneckerMap (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)).hom
      (cocycleClass _ _ (FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B)
        (closed m p F hε T hT hshort q B hB)) z =
    (kroneckerMap (TopCat.of (SphereLoop (m + 1))) q).hom (cocycleClass _ q B hB)
      (((operation m p F hε T hT hshort (a := a)).homology q).hom z) := by
  have h := DegreeLoweringCochainPullback.pairing (operation m p F hε T hT hshort (a := a)) q B hB z
  have he := cocycleClass_congr (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)
    (cochain_eq m p F hε T hT hshort q B)
    (DegreeLoweringCochainPullback.closed (operation m p F hε T hT hshort (a := a)) q B hB)
    (closed m p F hε T hT hshort q B hB)
  exact (congrArg
    (fun c : cohomologyZMod2 (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q) =>
      (kroneckerMap _ ((m + p) + q)).hom c z) he).symm.trans h

theorem canonical_pairing (q : ℕ)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0)
    (z : PoolCap.homology (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)) :
    (kroneckerMap (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q)).hom
      (cocycleClass _ _ (FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B)
        (closed m p F hε T hT hshort q B hB)) z =
    (kroneckerMap (TopCat.of (SphereLoop (m + 1))) q).hom (cocycleClass _ q B hB)
      ((PoolCap.push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε))) q).hom
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).homology q).hom z)) := by
  have h := pairing m p F hε T hT hshort q B hB z
  rw [operation, DegreeLoweringHomology.Map.post_homology] at h
  exact h

theorem class_eq_of_class_eq (q : ℕ)
    (B B' : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0)
    (hB' : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B' = 0)
    (hclass : cocycleClass _ q B hB = cocycleClass _ q B' hB') :
    cocycleClass _ _ (FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B)
      (closed m p F hε T hT hshort q B hB) =
    cocycleClass _ _ (FilteredGeometricTimeCup.canonicalCochain m p F hε a T q B')
      (closed m p F hε T hT hshort q B' hB') := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  rw [pairing m p F hε T hT hshort q B hB z,
    pairing m p F hε T hT hshort q B' hB' z, hclass]

end
end Finsler.FilteredCanonicalCutPairing
