module

public import Finsler.Topology.ConstantThomUnit
public import Finsler.Analysis.FilteredPaddingHomotopy

/-! Compare the actual near-join with the second-loop projection on constant-first pairs.
Both the padding removal and the original alignment correction stay in the specified cut. -/

@[expose] public section

namespace Finsler.ConstantJoinHomotopy

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1NearJoin Finsler.H1FiberBase Finsler.BorelEvaluation Finsler.BorelLoop
open Finsler.CochainComparison Finsler.ConstantThomUnit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def corrected {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    C(neighborhood F p hq hε, lev F (q + ε)) :=
  (correctedSecond F p hq hε).comp (restriction F p hq hε).hom

def joined {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    C(neighborhood F p hq hε, lev F (p + (q + ε))) :=
  (nearJoin F hp hq hε).comp (restriction F p hq hε).hom

def original {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    C(neighborhood F p hq hε, lev F (p + (q + ε))) :=
  (FilteredPaddingHomotopy.inclusion F hp (add_pos hq hε)).comp
    ((originalSecond F p hq hε).comp (restriction F p hq hε).hom)

theorem corrected_point {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : neighborhood F p hq hε) :
    point (corrected F p hq hε z).val = z.val.1 := by
  apply Subtype.ext
  exact (corrected_basepoint F p hq hε (restriction F p hq hε z)).trans
    (congrArg Subtype.val (eval_constant z.val.1))

theorem join_congr {n : ℕ} (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (u w u' w' : SphereLoop n) (h : CompactH1Alignment.basepoint u = CompactH1Alignment.basepoint w)
    (h' : CompactH1Alignment.basepoint u' = CompactH1Alignment.basepoint w')
    (hu : u = u') (hw : w = w') :
    H1LoopJoin.join a ha0 ha1 u w h = H1LoopJoin.join a ha0 ha1 u' w' h' := by
  subst u'
  subst w'
  rfl

theorem joined_start {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    joined F hp hq hε = (FilteredPaddingHomotopy.start F hp (add_pos hq hε)).comp
      (corrected F p hq hε) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change (nearJoin F hp hq hε (restriction F p hq hε z)).val =
    (FilteredPaddingHomotopy.start F hp (add_pos hq hε) (corrected F p hq hε z)).val
  rw [FilteredPaddingHomotopy.start_join]
  let w := (corrected F p hq hε z).val
  have hm : CompactH1Alignment.basepoint (constantSphereLoop z.val.1) =
      CompactH1Alignment.basepoint w :=
    (corrected_basepoint F p hq hε (restriction F p hq hε z)).symm
  change H1LoopJoin.join (FilteredPaddingHomotopy.split p (q + ε))
      (FilteredPaddingHomotopy.split_pos hp (add_pos hq hε))
      (FilteredPaddingHomotopy.split_lt_one hp (add_pos hq hε))
      (constantSphereLoop z.val.1) w hm = _
  exact join_congr _ _ _ _ _ _ _ _ _
    (congrArg constantSphereLoop (corrected_point F p hq hε z).symm) rfl

def homotopy {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    (joined F hp hq hε).Homotopy (original F hp hq hε) := by
  let P := (FilteredPaddingHomotopy.homotopy F hp (add_pos hq hε)).compContinuousMap
    (corrected F p hq hε)
  let C := (ContinuousMap.Homotopy.refl (FilteredPaddingHomotopy.inclusion F hp (add_pos hq hε))).comp
    ((correctionHomotopy F p hq hε).compContinuousMap (restriction F p hq hε).hom)
  exact (P.cast (joined_start F hp hq hε).symm rfl).trans C.symm

theorem homology_joined {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    PoolCap.push (TopCat.ofHom (joined F hp hq hε)) k =
      PoolCap.push (TopCat.ofHom (original F hp hq hε)) k := by
  let H : TopCat.Homotopy (TopCat.ofHom (joined F hp hq hε))
      (TopCat.ofHom (original F hp hq hε)) := homotopy F hp hq hε
  exact (H.toSSet.chainComplexMap Finsler.CochainComparison.coeff).homologyMap_eq k

end
end Finsler.ConstantJoinHomotopy

