module

public import Finsler.Topology.RightConstantThomUnit
public import Finsler.Analysis.FilteredRightPaddingHomotopy

/-! The actual near-join on constant-second pairs is homotopic to the first projection. -/

@[expose] public section

namespace Finsler.RightConstantJoinHomotopy

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1NearJoin Finsler.H1FiberBase Finsler.BorelEvaluation Finsler.BorelLoop
open Finsler.CochainComparison Finsler.RightConstantThomUnit
open Finsler.CompactH1Alignment Finsler.H1OrthogonalLength
open Finsler.SobolevReverse

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

theorem align_constant {n : ℕ} (x y : Sphere n) :
    align (constantSphereLoop x) y = constantSphereLoop y := by
  let A := NearbyRotor.rotor (basepoint (constantSphereLoop x)) (y : Ambient n)
  have he := basepoint_align (constantSphereLoop x) y
  change continuousRepresentative (rotateData A (constantData (x : Ambient n))) 0 =
    (y : Ambient n) at he
  rw [representative_rotateData A _ (by norm_num), continuousRepresentative_constantData _ (by norm_num)] at he
  apply SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (rotateData A (constantData (x : Ambient n))) t =
    continuousRepresentative (constantData (y : Ambient n)) t
  rw [representative_rotateData A _ t.property, continuousRepresentative_constantData _ t.property,
    continuousRepresentative_constantData _ t.property]
  exact he

def first {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : C(neighborhood F p hq hε, lev F p) :=
  ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

def joined {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    C(neighborhood F p hq hε, lev F (p + (q + ε))) :=
  (nearJoin F hp hq hε).comp (restriction F p hq hε).hom

def original {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    C(neighborhood F p hq hε, lev F (p + (q + ε))) :=
  (FilteredRightPaddingHomotopy.inclusion F hp (add_pos hq hε)).comp (first F p hq hε)

theorem corrected_constant {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : neighborhood F p hq hε) :
    (correctedSecond F p hq hε (restriction F p hq hε z)).val =
      constantSphereLoop (point z.val.1.val) := align_constant z.val.2 (point z.val.1.val)

theorem joined_start {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    joined F hp hq hε = (FilteredRightPaddingHomotopy.start F hp (add_pos hq hε)).comp
      (first F p hq hε) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change (nearJoin F hp hq hε (restriction F p hq hε z)).val =
    (FilteredRightPaddingHomotopy.start F hp (add_pos hq hε) (first F p hq hε z)).val
  rw [FilteredRightPaddingHomotopy.start_join]
  have hm : basepoint z.val.1.val =
      basepoint (correctedSecond F p hq hε (restriction F p hq hε z)).val :=
    (corrected_basepoint F p hq hε (restriction F p hq hε z)).symm
  change H1LoopJoin.join (FilteredPaddingHomotopy.split p (q + ε))
      (FilteredPaddingHomotopy.split_pos hp (add_pos hq hε))
      (FilteredPaddingHomotopy.split_lt_one hp (add_pos hq hε)) z.val.1.val
      (correctedSecond F p hq hε (restriction F p hq hε z)).val hm = _
  exact ConstantJoinHomotopy.join_congr _ _ _ _ _ _ _ _ _ rfl (corrected_constant F p hq hε z)

def homotopy {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    (joined F hp hq hε).Homotopy (original F hp hq hε) :=
  ((FilteredRightPaddingHomotopy.homotopy F hp (add_pos hq hε)).compContinuousMap
    (first F p hq hε)).cast (joined_start F hp hq hε).symm rfl

theorem homology_joined {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    PoolCap.push (TopCat.ofHom (joined F hp hq hε)) k =
      PoolCap.push (TopCat.ofHom (original F hp hq hε)) k := by
  let H : TopCat.Homotopy (TopCat.ofHom (joined F hp hq hε))
      (TopCat.ofHom (original F hp hq hε)) := homotopy F hp hq hε
  exact (H.toSSet.chainComplexMap Finsler.CochainComparison.coeff).homologyMap_eq k

end
end Finsler.RightConstantJoinHomotopy
