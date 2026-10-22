module

public import Finsler.Topology.FilteredLoopProduct
public import Finsler.Topology.SupportedCapHomology
public import Finsler.Topology.DiagonalPullbackClass

/-! The actual filtered loop-pair operation on homology, with its genuine
diagonal cap comparison before the near-join. A bilinear loop product from
an external product, the absolute unit and cut--join interchange are separate. -/

@[expose] public section

namespace Finsler.FilteredLoopProductHomology

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop
open Finsler.CochainComparison Finsler.H1NearJoin Finsler.SmallChainCarrier
open Finsler.FilteredLoopProduct Finsler.SphereTopClass

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def thomOperation (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    DegreeLoweringHomology.Map (chains (loopPairs F p q))
      (chains (TopCat.of (tube F p hq hε))) n where
  component k := thomCut hn F p hq hε k
  comm k := thomCut_boundary hn F p hq hε k

def productOperation (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    DegreeLoweringHomology.Map (chains (loopPairs F p q))
      (chains (TopCat.of (lev F (p + (q + ε))))) n where
  component k := FilteredLoopProduct.product hn F hp hq hε k
  comm k := product_boundary hn F hp hq hε k

def homology (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :=
  (productOperation hn F hp hq hε).homology k

theorem product_homology_factor (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    homology hn F hp hq hε k = (thomOperation hn F p hq hε).homology k ≫
      HomologicalComplex.homologyMap (NearJoinChains.joinChainMap F hp hq hε) k := by
  let t := thomOperation hn F p hq hε
  let j := NearJoinChains.joinChainMap F hp hq hε
  calc
    _ = (t.post j).homology k := by
      apply DegreeLoweringHomology.Map.homology_eq_of_components
      intro r
      rfl
    _ = _ := t.post_homology j k

theorem homologyπ_product (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    (chains (loopPairs F p q)).homologyπ (n + k) ≫ homology hn F hp hq hε k =
      (productOperation hn F hp hq hε).cycles k ≫
        (chains (TopCat.of (lev F (p + (q + ε))))).homologyπ k :=
  (productOperation hn F hp hq hε).homologyπ_homology k

theorem thom_homology_comparison (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    (thomOperation hn F p hq hε).homology k ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map
            (SupportedCap.subspaceMap (loopPairs F p q) (tube F p hq hε))) coeff) k =
      ModuleCat.ofHom (PoolCap.cap (loopPairs F p q) n k (n + k) rfl
        ((cohPullback (leftEvaluation F p q) n).hom (topClass n hn) +
          (cohPullback (rightEvaluation F p q) n).hom (topClass n hn))) := by
  let X := loopPairs F p q
  let f := leftEvaluation F p q
  let g := rightEvaluation F p q
  let A := DiagonalPullbackCut.exclusion f g
  let B := tube F p hq hε
  let φ := DiagonalPullbackCut.cocycle hn f g
  have hA : IsOpen A := DiagonalPullbackCut.exclusion_open f g
  have hB : IsOpen B := tube_open F p hq hε
  have hc : A ∪ B = Set.univ :=
    DiagonalPullbackCut.neighborhood_cover f g B (diagonal_in_tube F p hq hε)
  have hs : cochainPullback (SupportedCap.subspaceMap X A) n φ = 0 :=
    DiagonalPullbackCut.cocycle_supported hn f g
  have hφ : cochainCoboundary (ZMod 2) X n φ = 0 := DiagonalPullbackCut.cocycle_closed hn f g
  have he : (thomOperation hn F p hq hε).homology k =
      (SupportedCapHomology.operation X A B hA hB hc n φ hs hφ).homology k := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro r
    rfl
  have hclass : cocycleClass X n φ hφ =
      (cohPullback f n).hom (topClass n hn) + (cohPullback g n).hom (topClass n hn) :=
    DiagonalPullbackClass.cocycle_class hn f g
  rw [he, SupportedCapHomology.ambient_comparison, hclass]

end
end Finsler.FilteredLoopProductHomology
