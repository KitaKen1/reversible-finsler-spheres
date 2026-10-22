module

public import Finsler.Topology.RightSphereDiagonalCap
public import Finsler.Topology.FilteredLeftUnit

/-! The genuine Thom-cut calculation when the constant-loop candidate is on the right. -/

@[expose] public section

namespace Finsler.RightConstantThomUnit

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.H1NearJoin
open Finsler.FilteredLoopProduct Finsler.SphereUnitCandidate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def embedding {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) :
    TopCat.of (lev F p) ⊗ sphere n ⟶ loopPairs F p q :=
  𝟙 (TopCat.of (lev F p)) ⊗ₘ constantMap F q

theorem embedding_left {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) :
    embedding F p q ≫ leftEvaluation F p q =
      fst (TopCat.of (lev F p)) (sphere n) ≫ evaluation F p := by ext z : 1; rfl

theorem embedding_right {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) :
    embedding F p q ≫ rightEvaluation F p q = snd (TopCat.of (lev F p)) (sphere n) := by
  ext z : 1
  exact eval_constant z.2

def neighborhood {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : Set (lev F p × sphere n) :=
  embedding F p q ⁻¹' tube F p hq hε

theorem neighborhood_open {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : IsOpen (neighborhood F p hq hε) :=
  (tube_open F p hq hε).preimage (embedding F p q).hom.continuous

theorem neighborhood_diagonal {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : TopCat.of (lev F p) ⊗ sphere n)
    (hz : (fst (TopCat.of (lev F p)) (sphere n) ≫ evaluation F p) z =
      (snd (TopCat.of (lev F p)) (sphere n)) z) : z ∈ neighborhood F p hq hε := by
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
  RightSphereDiagonalCap.operation n hn (TopCat.of (lev F p)) (evaluation F p)
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
  have hs : (DiagonalCutNaturality.operation hn
      (fst (TopCat.of (lev F p)) (sphere n) ≫ evaluation F p) (snd (TopCat.of (lev F p)) (sphere n))
      (neighborhood F p hq hε) (neighborhood_open F p hq hε)
      (neighborhood_diagonal F p hq hε)).homology k =
      (sphereOperation hn F p hq hε).homology k := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro j
    rfl
  rw [ht, hs] at he
  exact he

theorem unit_cross {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p q : ℝ)
    (k : ℕ) (x : PoolCap.homology (TopCat.of (lev F p)) k) :
    FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) k n
        (n + k) (Nat.add_comm k n) x (candidate hn F q) =
      (PoolCap.push (embedding F p q) (n + k)).hom
        (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (sphere n) k n (n + k)
          (Nat.add_comm k n) x (fundamental n hn)) := by
  have he := CrossProjectionZero.cross_naturality_apply (𝟙 (TopCat.of (lev F p)))
    (constantMap F q) k n (n + k) (Nat.add_comm k n) x (fundamental n hn)
  have hi : (PoolCap.push (𝟙 (TopCat.of (lev F p))) k).hom x = x := by
    rw [PoolCap.push, CategoryTheory.Functor.map_id]
    rfl
  rw [hi] at he
  exact he

theorem thom_factor {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) (x : PoolCap.homology (TopCat.of (lev F p)) k) :
    ((FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k).hom
        (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) k n
          (n + k) (Nat.add_comm k n) x (candidate hn F q)) =
      (PoolCap.push (restriction F p hq hε) k).hom
        (((sphereOperation hn F p hq hε).homology k).hom
          (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (sphere n) k n (n + k)
            (Nat.add_comm k n) x (fundamental n hn))) := by
  rw [unit_cross]
  exact ConcreteCategory.congr_hom (thom_naturality hn F p hq hε k) _

theorem restriction_projection {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    restriction F p hq hε ≫
        (SupportedCap.subspaceMap (loopPairs F p q) (tube F p hq hε) ≫
          fst (TopCat.of (lev F p)) (TopCat.of (lev F q))) =
      SupportedCap.subspaceMap (TopCat.of (lev F p) ⊗ sphere n) (neighborhood F p hq hε) ≫
        fst (TopCat.of (lev F p)) (sphere n) := by ext z : 1; rfl

theorem thom_unit_projection {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) (x : PoolCap.homology (TopCat.of (lev F p)) k) :
    (PoolCap.push (SupportedCap.subspaceMap (loopPairs F p q) (tube F p hq hε) ≫
        fst (TopCat.of (lev F p)) (TopCat.of (lev F q))) k).hom
      (((FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k).hom
        (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) k n
          (n + k) (Nat.add_comm k n) x (candidate hn F q))) = x := by
  rw [thom_factor]
  let z := ((sphereOperation hn F p hq hε).homology k).hom
    (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (sphere n) k n (n + k)
      (Nat.add_comm k n) x (fundamental n hn))
  have he := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff).map_comp
      (restriction F p hq hε)
      (SupportedCap.subspaceMap (loopPairs F p q) (tube F p hq hε) ≫
        fst (TopCat.of (lev F p)) (TopCat.of (lev F q)))) z
  rw [restriction_projection] at he
  exact he.symm.trans (RightSphereDiagonalCap.cut_projection n hn (TopCat.of (lev F p))
    (evaluation F p) (neighborhood F p hq hε) (neighborhood_open F p hq hε)
    (neighborhood_diagonal F p hq hε) k x)

end
end Finsler.RightConstantThomUnit
