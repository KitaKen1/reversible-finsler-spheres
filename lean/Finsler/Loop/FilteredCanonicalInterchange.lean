module

public import Finsler.Loop.CompactFamilyInterchangeValue
public import Finsler.Loop.CompactHomologyLift
public import Finsler.Topology.CrossProjectionZero

/-! Genuine filtered canonical cut/product interchange on ALL actual
singular homology classes in arbitrary real strict input sublevels.
Each class is lifted to an actual compact subspace by the compact-support
colimit, and the proved compact-family operation is transported by actual
external-product naturality. No compact-lift hypothesis is assumed. -/

@[expose] public section
namespace Finsler.FilteredCanonicalInterchange
open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree TopologicalSpace
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge
open Finsler.FarNormalizedDiagonalCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000


theorem value {m : ℕ} (F : ReversibleMetric (m + 1)) {ε : ℝ} (hε : 0 < ε) (hm : 1 ≤ m)
    (p : ℕ) (L a b A : ℝ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0)
    (hab : a + b < A) (i j k : ℕ) (hij : i + j = (m + 1) + k) (hi : 1 < i)
    (x : PoolCap.homology (lengthSpace F a) ((m + p) + i)) (y : PoolCap.homology (lengthSpace F b) j) :
    ((CanonicalAfterLengthProduct.operation F hab hε p T hT hshort).homology k).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) ((m + p) + i) j
        (((m + 1) + (m + p)) + k) (by omega) x y) =
    StrictLengthProductBudget.product F (L := L) hab hε (dim_pos m) i j k hij
      (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).homology i).hom x) y := by
  obtain ⟨K, xK, hx⟩ := CompactHomologyLift.exists_lift (lengthSpace F a) ((m + p) + i) x
  obtain ⟨M, yM, hy⟩ := CompactHomologyLift.exists_lift (lengthSpace F b) j y
  let α : C(K, SphereLoop (m + 1)) := ⟨fun z => z.val.val, continuous_subtype_val.comp continuous_subtype_val⟩
  let β : C(M, SphereLoop (m + 1)) := ⟨fun z => z.val.val, continuous_subtype_val.comp continuous_subtype_val⟩
  have hα : ∀ z, SobolevLength.length F (α z) < a := fun z => z.val.property
  have hβ : ∀ z, SobolevLength.length F (β z) < b := fun z => z.val.property
  have hleft : StrictLengthProductFamilies.leftInput α F a hα = SupportedCap.subspaceMap (lengthSpace F a) (K : Set (lengthSpace F a)) := by ext z : 1; rfl
  have hright : StrictLengthProductFamilies.rightInput β F b hβ = SupportedCap.subspaceMap (lengthSpace F b) (M : Set (lengthSpace F b)) := by ext z : 1; rfl
  have hx' : (PoolCap.push (StrictLengthProductFamilies.leftInput α F a hα) ((m + p) + i)).hom xK = x := by
    rw [hleft]
    exact hx
  have hy' : (PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j).hom yM = y := by
    rw [hright]
    exact hy
  have he := CompactFamilyInterchangeValue.value α β F hε hm p L a b A T hT hshort hα hβ hab i j k hij hi xK yM
  have hn := CrossProjectionZero.cross_naturality_apply (StrictLengthProductFamilies.leftInput α F a hα)
    (StrictLengthProductFamilies.rightInput β F b hβ) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) xK yM
  rw [hx', hy'] at hn
  have hfirst : (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
      (push (CompactInputShortMaps.family α F a hα))).homology i).hom xK =
    ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).homology i).hom x := by
    rw [DegreeLoweringHomology.Map.pre_homology]
    change ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).homology i).hom
      ((PoolCap.push (StrictLengthProductFamilies.leftInput α F a hα) ((m + p) + i)).hom xK) = _
    rw [hx']
  rw [hfirst, hy'] at he
  exact (congrArg (fun z => ((CanonicalAfterLengthProduct.operation F hab hε p T hT hshort).homology k).hom z) hn).trans he

end
end Finsler.FilteredCanonicalInterchange
