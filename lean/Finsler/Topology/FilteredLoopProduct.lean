module

public import Finsler.Topology.DiagonalPullbackCut
public import Finsler.Topology.NearJoinChains

/-! Actual degree-n filtered loop product on singular chains of pairs of loops.
The diagonal Thom cut lands in the controlled near-diagonal tube, then the
actual near-join lands in the original p+q+ε energy cut. No unit, associativity,
self-cut interchange, resonance, or uniform filling theorem is asserted. -/

@[expose] public section

namespace Finsler.FilteredLoopProduct

open CategoryTheory AlgebraicTopology
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy Finsler.H1FiberBase
open Finsler.H1NearJoin Finsler.SmallChainCarrier

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def loopPairs (F : ReversibleMetric n) (p q : ℝ) : TopCat.{0} :=
  TopCat.of (lev F p × lev F q)

def leftEvaluation (F : ReversibleMetric n) (p q : ℝ) : loopPairs F p q ⟶ sphere n :=
  TopCat.ofHom ⟨fun z => point z.1.val,
    continuous_point.comp (continuous_subtype_val.comp continuous_fst)⟩

def rightEvaluation (F : ReversibleMetric n) (p q : ℝ) : loopPairs F p q ⟶ sphere n :=
  TopCat.ofHom ⟨fun z => point z.2.val,
    continuous_point.comp (continuous_subtype_val.comp continuous_snd)⟩

theorem tube_open (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : IsOpen (tube F p hq hε) :=
  isOpen_lt
    ((basepoint_continuous.comp (continuous_subtype_val.comp continuous_snd)).dist
      (basepoint_continuous.comp (continuous_subtype_val.comp continuous_fst))) continuous_const

theorem diagonal_in_tube (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : loopPairs F p q)
    (hz : leftEvaluation F p q z = rightEvaluation F p q z) : z ∈ tube F p hq hε := by
  have he : basepoint z.1.val = basepoint z.2.val := congrArg Subtype.val hz
  change dist (basepoint z.2.val) (basepoint z.1.val) < radius F hq hε
  rw [he, dist_self]
  exact (radius_spec F hq hε).1

def thomCut (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    (chains (loopPairs F p q)).X (n + k) ⟶ (chains (TopCat.of (tube F p hq hε))).X k :=
  DiagonalPullbackCut.cut hn (leftEvaluation F p q) (rightEvaluation F p q)
    (tube F p hq hε) (tube_open F p hq hε) (diagonal_in_tube F p hq hε) k

theorem thomCut_boundary (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    thomCut hn F p hq hε (k + 1) ≫
        (chains (TopCat.of (tube F p hq hε))).d (k + 1) k =
      (chains (loopPairs F p q)).d (n + (k + 1)) (n + k) ≫ thomCut hn F p hq hε k :=
  DiagonalPullbackCut.cut_boundary hn (leftEvaluation F p q) (rightEvaluation F p q)
    (tube F p hq hε) (tube_open F p hq hε) (diagonal_in_tube F p hq hε) k

def product (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    (chains (loopPairs F p q)).X (n + k) ⟶
      (chains (TopCat.of (lev F (p + (q + ε))))).X k :=
  thomCut hn F p hq hε k ≫ (NearJoinChains.joinChainMap F hp hq hε).f k

theorem product_boundary (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    product hn F hp hq hε (k + 1) ≫
        (chains (TopCat.of (lev F (p + (q + ε))))).d (k + 1) k =
      (chains (loopPairs F p q)).d (n + (k + 1)) (n + k) ≫ product hn F hp hq hε k := by
  rw [product, Category.assoc, NearJoinChains.join_boundary, ← Category.assoc,
    thomCut_boundary, Category.assoc]
  rfl


end
end Finsler.FilteredLoopProduct
