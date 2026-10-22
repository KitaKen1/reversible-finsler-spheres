module

public import Finsler.Loop.StrictLengthProductJoinComparison

/-! A genuine length-filtered bilinear product is induced by the specified
diagonal Thom cut on the original length-pair space followed by the actual
raw half-time first join. All equalities live in the strict length target. -/

@[expose] public section
namespace Finsler.StrictLengthProductGeometricFactor

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge Finsler.StrictLengthLoopProduct
open Finsler.LengthProductNormalizationGeometry Finsler.CompactH1Alignment
open Finsler.StrictLengthProductJoinComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
  {ε : ℝ} (hε : 0 < ε)

theorem diagonal_in_common (z : pairSpace F p q)
    (hz : leftEvaluation F p q z = rightEvaluation F p q z) : z ∈ commonTube F p q hp hq hε := by
  have he := congrArg Subtype.val hz
  change basepoint z.1.val = basepoint z.2.val at he
  change dist (basepoint z.1.val) (basepoint z.2.val) < radius F p q hp hq hε
  rw [he, dist_self]
  exact radius_pos F p q hp hq hε

def commonThom (hn : 1 ≤ n) := DiagonalCutNaturality.operation hn
  (leftEvaluation F p q) (rightEvaluation F p q) (commonTube F p q hp hq hε)
  (commonTube_open F p q hp hq hε) (diagonal_in_common F p q hp hq hε)

theorem thom_refine (hn : 1 ≤ n) (k : ℕ) :
    (StrictLengthProductThomFactor.thomOperation F p hq hε hn).homology k =
    (commonThom F p q hp hq hε hn).homology k ≫
      HomologicalComplex.homologyMap (push (toProductTube F p q hp hq hε)) k := by
  have he := DiagonalCutNaturality.homology_naturality hn (𝟙 (pairSpace F p q))
    (leftEvaluation F p q) (rightEvaluation F p q)
    (commonTube F p q hp hq hε) (StrictLengthProductThomFactor.tube F p hq hε)
    (commonTube_open F p q hp hq hε) (StrictLengthProductThomFactor.tube_open F p hq hε)
    (diagonal_in_common F p q hp hq hε) (StrictLengthProductThomFactor.diagonal_in_tube F p hq hε)
    (commonTube_sub_product F p q hp hq hε) k
  change HomologicalComplex.homologyMap (push (𝟙 (pairSpace F p q))) (n + k) ≫
      (StrictLengthProductThomFactor.thomOperation F p hq hε hn).homology k =
    (commonThom F p q hp hq hε hn).homology k ≫
      HomologicalComplex.homologyMap (push (toProductTube F p q hp hq hε)) k at he
  have hid : push (𝟙 (pairSpace F p q)) = 𝟙 (chains (pairSpace F p q)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (pairSpace F p q))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.homologyMap_id, Category.id_comp] at he
  exact he

def geometricOperation (hn : 1 ≤ n) :=
  (commonThom F p q hp hq hε hn).post (push (rawJoin F p q hp hq hε))

theorem positive_operation (hn : 1 ≤ n) (k : ℕ) :
    (positiveOperation F hn hp hq hε).homology k =
    (geometricOperation F p q hp hq hε hn).homology k := by
  rw [geometricOperation, DegreeLoweringHomology.Map.post_homology,
    StrictLengthProductThomFactor.positive_homology_factor F p hq hε hp hn k,
    thom_refine F p q hp hq hε hn k, Category.assoc,
    StrictLengthProductJoinComparison.homology_eq F p q hp hq hε k]

theorem operation (hn : 1 ≤ n) (k : ℕ) :
    (StrictLengthLoopProduct.operation F hn hε).homology k =
    (geometricOperation F p q hp hq hε hn).homology k := by
  rw [StrictLengthLoopProduct.operation_pos F hn hp hq hε]
  exact positive_operation F p q hp hq hε hn k

theorem product_factor (hn : 1 ≤ n) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    StrictLengthLoopProduct.product F hn hε i j k h x y =
    (HomologicalComplex.homologyMap (push (rawJoin F p q hp hq hε)) k).hom
      (((commonThom F p q hp hq hε hn).homology k).hom
        (FilteredBilinearLoopProduct.cross (lengthSpace F p) (lengthSpace F q) i j (n + k) h x y)) := by
  rw [StrictLengthProductCompatibility.chain_apply, operation F p q hp hq hε hn k]
  rw [geometricOperation, DegreeLoweringHomology.Map.post_homology]
  rfl

end
end Finsler.StrictLengthProductGeometricFactor
