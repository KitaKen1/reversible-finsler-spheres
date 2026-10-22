module

public import Finsler.Loop.CanonicalAfterLengthProductValue
public import Finsler.Loop.CanonicalGlobalSelfCutFiltered
public import Finsler.Loop.LengthFilteredLoopRotation
public import Finsler.Loop.SplitPairHomologyKernel

/-! The ACTUAL full image of the ORIGINAL product-then-cut is the
actual global D_T of the SAME genuine strict-length product. Both
the source-degree reassociation and output-length equality transport
are retained, using the already checked original cross evaluation. -/
@[expose] public section
namespace Finsler.CanonicalAfterLengthProductFull
open CategoryTheory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem transport_full_apply {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (h : a = b)
    (k : ℕ) (z : homologyZMod2 (lengthSpace F a) k) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) k).hom
      ((homologyMap (eqToHom (congrArg (fun c : ℝ => chains (lengthSpace F c)) h)) k).hom z) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) k).hom z := by
  subst b
  simp only [eqToHom_refl, homologyMap_id, ModuleCat.hom_id, LinearMap.id_apply]

theorem value {m : ℕ} (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) {a b A L ε : ℝ}
    (hab : a + b < A) (hε : 0 < ε) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hs : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1))
      (SelfCutOscillation.short F L)) p T = 0)
    (i j k : ℕ) (hij : i + j = ((m + 1) + (m + p)) + k)
    (x : PoolCap.homology (lengthSpace F a) i) (y : PoolCap.homology (lengthSpace F b) j) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (A - L + 5 * ε)) k).hom
      (((CanonicalAfterLengthProduct.operation F hab hε p T hT hs).homology k).hom
        (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j
          (((m + 1) + (m + p)) + k) hij x y)) =
    (CanonicalGlobalSelfCut.map m p k (cocycleClass _ p T hT)).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (a + (b + ε))) ((m + p) + k)).hom
        (StrictLengthLoopProduct.product F (by omega) hε i j ((m + p) + k) (by omega) x y)) := by
  let w := ((OriginalLengthProductBudget.operation F (CanonicalAfterLengthProduct.input_budget hab hε)
    (by omega) hε).homology ((m + p) + k)).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j
        ((m + 1) + ((m + p) + k)) (by omega) x y)
  have ht := transport_full_apply F
    (by ring : (A + 2 * ε) - L + 3 * ε = A - L + 5 * ε) k
    (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hs).homology k).hom w)
  have hg := CanonicalGlobalSelfCutFiltered.original_filtered m hm p F hε T hT hs k w
  have hw : (homologyPushZMod2 (LengthFilteredLoopRotation.full F (A + 2 * ε)) ((m + p) + k)).hom w =
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a + (b + ε))) ((m + p) + k)).hom
        (StrictLengthLoopProduct.product F (by omega) hε i j ((m + p) + k) (by omega) x y) := by
    dsimp only [w]
    rw [OriginalLengthProductBudget.operation, DegreeLoweringHomology.Map.post_homology]
    change (homologyPushZMod2 (LengthFilteredLoopRotation.full F (A + 2 * ε)) ((m + p) + k)).hom
      ((homologyPushZMod2 (OriginalLengthProductBudget.outputInclusion F
        (CanonicalAfterLengthProduct.input_budget hab hε)) ((m + p) + k)).hom
        (((StrictLengthLoopProduct.operation F (by omega) hε).homology ((m + p) + k)).hom
          (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F b) i j
            ((m + 1) + ((m + p) + k)) (by omega) x y))) = _
    rw [push_comp_apply]
    have hf : OriginalLengthProductBudget.outputInclusion F
        (CanonicalAfterLengthProduct.input_budget hab hε) ≫
          LengthFilteredLoopRotation.full F (A + 2 * ε) =
        LengthFilteredLoopRotation.full F (a + (b + ε)) := by ext u : 1; rfl
    rw [hf]
    exact congrArg (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a + (b + ε))) ((m + p) + k)).hom
      (StrictLengthProductCompatibility.chain_apply F (by omega) hε i j ((m + p) + k) (by omega) x y).symm
  exact (congrArg (homologyPushZMod2 (LengthFilteredLoopRotation.full F (A - L + 5 * ε)) k).hom
    (CanonicalAfterLengthProductValue.value F hab hε p T hT hs i j k hij x y)).trans
      (ht.trans (hg.trans (congrArg (CanonicalGlobalSelfCut.map m p k (cocycleClass _ p T hT)).hom hw)))

end
end Finsler.CanonicalAfterLengthProductFull
