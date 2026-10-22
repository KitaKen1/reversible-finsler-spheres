module

public import Finsler.Loop.CompactFamilyFilteredInterchange

/-! The proved actual compact-family interchange evaluated on genuine
homology classes, retaining the real external cross and product. -/

@[expose] public section
namespace Finsler.CompactFamilyInterchangeValue
open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge
open Finsler.FarNormalizedDiagonalCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000


theorem value {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (F : ReversibleMetric (m + 1))
    {ε : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (p : ℕ) (L a b A : ℝ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0)
    (hA : ∀ x, SobolevLength.length F (α x) < a) (hβ : ∀ y, SobolevLength.length F (β y) < b) (hab : a + b < A)
    (i j k : ℕ) (hij : i + j = (m + 1) + k) (hi : 1 < i)
    (x : PoolCap.homology (TopCat.of P) ((m + p) + i)) (y : PoolCap.homology (TopCat.of Q) j) :
    ((CanonicalAfterLengthProduct.operation F hab hε p T hT hshort).homology k).hom
      ((PoolCap.push (StrictLengthProductFamilies.pairInput α β F a b hA hβ) (((m + 1) + (m + p)) + k)).hom
        (FilteredBilinearLoopProduct.cross (TopCat.of P) (TopCat.of Q) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) x y)) =
    StrictLengthProductBudget.product F (L := L) hab hε (dim_pos m) i j k hij
      ((((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
        (push (CompactInputShortMaps.family α F a hA))).homology i).hom x)
      ((PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j).hom y) := by
  rw [StrictLengthProductBudget.chain_apply, FilteredBilinearLoopProduct.cross_apply]
  have he := ConcreteCategory.congr_hom
    (CompactFamilyFilteredInterchange.homology_eq α β F hε hm p L a b A T hT hshort hA hβ hab i j k hij hi)
    (x ⊗ₜ[ZMod 2] y)
  rw [DegreeLoweringHomology.Map.pre_homology] at he
  change _ = ((StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k).hom
    ((FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij).hom
      (((((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
        (push (CompactInputShortMaps.family α F a hA))).homology i) ⊗ₘ
          PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j) (x ⊗ₜ[ZMod 2] y))) at he
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul] at he
  exact he

end
end Finsler.CompactFamilyInterchangeValue
