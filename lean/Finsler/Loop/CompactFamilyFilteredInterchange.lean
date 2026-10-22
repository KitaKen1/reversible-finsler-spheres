module

public import Finsler.Loop.CompactJoinCanonicalAfterProduct
public import Finsler.Loop.UniformNativeCanonicalJoinedFamily

/-! Genuine high-first-degree filtered interchange on arbitrary real
strictly bounded compact H1 families. Actual canonical D_T follows the
genuine strict-length product on the left; the right is the genuine
product of canonical D_T(first) and beta. Native support radii and every
refinement are supplied internally before all tested cochains/bounds. -/

@[expose] public section
namespace Finsler.CompactFamilyFilteredInterchange

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

theorem homology_eq {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (F : ReversibleMetric (m + 1))
    {ε : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) :
    ∀ (p : ℕ) (L a b A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
      (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0)
      (hA : ∀ x, SobolevLength.length F (α x) < a) (hβ : ∀ y, SobolevLength.length F (β y) < b) (hab : a + b < A)
      (i j k : ℕ) (hij : i + j = (m + 1) + k), 1 < i →
      FilteredBilinearLoopProduct.crossMap (TopCat.of P) (TopCat.of Q) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
        ((CanonicalAfterLengthProduct.operation F hab hε p T hT hshort).pre
          (push (StrictLengthProductFamilies.pairInput α β F a b hA hβ))).homology k =
      (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
        (push (CompactInputShortMaps.family α F a hA))).homology i ⊗ₘ PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j) ≫
      FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij ≫
        (StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k := by
  obtain ⟨h, h4, hr, hradius⟩ := SingleCutCanonicalAnyRadius.native_radii F hε
  obtain ⟨R, hRp, _hRc, hR, κ, hκ, hκR, s, hs, hs1, θ, hθ, _hθ1, ζ, hζ, _hζ1,
      σ, hσ, _hσ1, index, hindex, hsmall, htested⟩ :=
    UniformNativeCanonicalJoinedFamily.exists_uniform α β h h4 hr F hε (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1) hradius hm
  intro p L a b A T hT hshort hA hβ hab i j k hij hi
  obtain ⟨hg, D, hΓ, hfull, hfirst⟩ := htested p L a b A T hT hshort hA hβ hab
  have hc := CompactJoinCanonicalAfterProduct.homology_eq α β F hab hε hA hβ R hR hκ hκR hΓ p T hT hshort
    D.full hfull hm k
  rw [← hc]
  exact hfirst i j k hij hi

end
end Finsler.CompactFamilyFilteredInterchange
