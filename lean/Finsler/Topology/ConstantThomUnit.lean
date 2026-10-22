module

public import Finsler.Topology.DiagonalCutNaturality
public import Finsler.Topology.SphereDiagonalCap

/-! Apply the genuine neighborhood Thom-cut naturality to actual constant loops.
The joined unit law still requires deletion of the constant interval in strong H1. -/

@[expose] public section

namespace Finsler.ConstantThomUnit

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.H1NearJoin
open Finsler.FilteredLoopProduct Finsler.SphereUnitCandidate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def embedding {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) :
    sphere n ⊗ TopCat.of (lev F q) ⟶ loopPairs F p q :=
  constantMap F p ⊗ₘ 𝟙 (TopCat.of (lev F q))

theorem embedding_left {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) :
    embedding F p q ≫ leftEvaluation F p q = fst (sphere n) (TopCat.of (lev F q)) := by
  ext z : 1
  exact eval_constant z.1

theorem embedding_right {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) :
    embedding F p q ≫ rightEvaluation F p q =
      snd (sphere n) (TopCat.of (lev F q)) ≫ evaluation F q := by
  ext z : 1
  rfl

def neighborhood {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : Set (sphere n × lev F q) :=
  embedding F p q ⁻¹' tube F p hq hε

theorem neighborhood_open {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : IsOpen (neighborhood F p hq hε) :=
  (tube_open F p hq hε).preimage (embedding F p q).hom.continuous

theorem neighborhood_diagonal {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : sphere n ⊗ TopCat.of (lev F q))
    (hz : (fst (sphere n) (TopCat.of (lev F q))) z =
      (snd (sphere n) (TopCat.of (lev F q)) ≫ evaluation F q) z) :
    z ∈ neighborhood F p hq hε := by
  apply diagonal_in_tube F p hq hε (embedding F p q z)
  change (embedding F p q ≫ leftEvaluation F p q) z =
    (embedding F p q ≫ rightEvaluation F p q) z
  rw [embedding_left, embedding_right]
  exact hz

def restriction {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    TopCat.of (neighborhood F p hq hε) ⟶ TopCat.of (tube F p hq hε) :=
  SupportedCapNaturality.restriction (embedding F p q) (neighborhood F p hq hε)
    (tube F p hq hε) (fun _ hx => hx)

def sphereOperation {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :=
  SphereDiagonalCap.operation n hn (TopCat.of (lev F q)) (evaluation F q)
    (neighborhood F p hq hε) (neighborhood_open F p hq hε) (neighborhood_diagonal F p hq hε)

theorem thom_naturality {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    PoolCap.push (embedding F p q) (n + k) ≫
        (FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k =
      (sphereOperation hn F p hq hε).homology k ≫ PoolCap.push (restriction F p hq hε) k := by
  have he := DiagonalCutNaturality.homology_naturality hn (embedding F p q)
    (leftEvaluation F p q) (rightEvaluation F p q)
    (neighborhood F p hq hε) (tube F p hq hε)
    (neighborhood_open F p hq hε) (tube_open F p hq hε)
    (fun z hz => by
      apply neighborhood_diagonal F p hq hε z
      change (embedding F p q ≫ leftEvaluation F p q) z =
        (embedding F p q ≫ rightEvaluation F p q) z at hz
      simpa only [embedding_left, embedding_right] using hz)
    (diagonal_in_tube F p hq hε) (fun _ hx => hx) k
  simp only [embedding_left, embedding_right] at he
  have ht : (DiagonalCutNaturality.operation hn (leftEvaluation F p q) (rightEvaluation F p q)
      (tube F p hq hε) (tube_open F p hq hε) (diagonal_in_tube F p hq hε)).homology k =
      (FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro j
    rfl
  have hs : (DiagonalCutNaturality.operation hn (fst (sphere n) (TopCat.of (lev F q)))
      (snd (sphere n) (TopCat.of (lev F q)) ≫ evaluation F q)
      (neighborhood F p hq hε) (neighborhood_open F p hq hε)
      (neighborhood_diagonal F p hq hε)).homology k =
      (sphereOperation hn F p hq hε).homology k := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro j
    rfl
  rw [ht, hs] at he
  exact he

theorem unit_cross {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p q : ℝ)
    (k : ℕ) (y : PoolCap.homology (TopCat.of (lev F q)) k) :
    FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) n k
        (n + k) rfl (candidate hn F p) y =
      (PoolCap.push (embedding F p q) (n + k)).hom
        (FilteredBilinearLoopProduct.cross (sphere n) (TopCat.of (lev F q)) n k (n + k) rfl
          (fundamental n hn) y) := by
  have he := CrossProjectionZero.cross_naturality_apply (constantMap F p)
    (𝟙 (TopCat.of (lev F q))) n k (n + k) rfl (fundamental n hn) y
  have hi : (PoolCap.push (𝟙 (TopCat.of (lev F q))) k).hom y = y := by
    rw [PoolCap.push, CategoryTheory.Functor.map_id]
    rfl
  rw [hi] at he
  exact he

theorem thom_factor {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) (y : PoolCap.homology (TopCat.of (lev F q)) k) :
    ((FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k).hom
        (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) n k
          (n + k) rfl (candidate hn F p) y) =
      (PoolCap.push (restriction F p hq hε) k).hom
        (((sphereOperation hn F p hq hε).homology k).hom
          (FilteredBilinearLoopProduct.cross (sphere n) (TopCat.of (lev F q)) n k (n + k) rfl
            (fundamental n hn) y)) := by
  rw [unit_cross]
  exact ConcreteCategory.congr_hom (thom_naturality hn F p hq hε k) _

theorem restriction_projection {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    restriction F p hq hε ≫
        (SupportedCap.subspaceMap (loopPairs F p q) (tube F p hq hε) ≫
          snd (TopCat.of (lev F p)) (TopCat.of (lev F q))) =
      SupportedCap.subspaceMap (sphere n ⊗ TopCat.of (lev F q)) (neighborhood F p hq hε) ≫
        snd (sphere n) (TopCat.of (lev F q)) := by
  ext z : 1
  rfl

theorem thom_unit_projection {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) (y : PoolCap.homology (TopCat.of (lev F q)) k) :
    (PoolCap.push (SupportedCap.subspaceMap (loopPairs F p q) (tube F p hq hε) ≫
        snd (TopCat.of (lev F p)) (TopCat.of (lev F q))) k).hom
      (((FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k).hom
        (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) n k
          (n + k) rfl (candidate hn F p) y)) = y := by
  rw [thom_factor]
  let x := ((sphereOperation hn F p hq hε).homology k).hom
    (FilteredBilinearLoopProduct.cross (sphere n) (TopCat.of (lev F q)) n k (n + k) rfl
      (fundamental n hn) y)
  have hmap := ((singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff).map_comp
    (restriction F p hq hε)
    (SupportedCap.subspaceMap (loopPairs F p q) (tube F p hq hε) ≫
      snd (TopCat.of (lev F p)) (TopCat.of (lev F q)))
  have hv := ConcreteCategory.congr_hom hmap x
  rw [restriction_projection] at hv
  exact hv.symm.trans (SphereDiagonalCap.cut_projection n hn (TopCat.of (lev F q))
    (evaluation F q) (neighborhood F p hq hε) (neighborhood_open F p hq hε)
    (neighborhood_diagonal F p hq hε) k y)

theorem thom_unit_ne_zero {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) (y : PoolCap.homology (TopCat.of (lev F q)) k)
    (hy : y ≠ 0) :
    ((FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k).hom
        (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) n k
          (n + k) rfl (candidate hn F p) y) ≠ 0 := by
  intro hz
  have he := thom_unit_projection hn F p hq hε k y
  rw [hz, map_zero] at he
  exact hy he.symm

end
end Finsler.ConstantThomUnit

