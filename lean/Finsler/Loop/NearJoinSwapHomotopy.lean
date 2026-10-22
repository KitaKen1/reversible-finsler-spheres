module

public import Finsler.Loop.HalfJoinTimeShift
public import Finsler.Loop.FilteredLoopTimeShift
public import Finsler.Topology.JoinLengthComparison

/-! A genuine length-controlled interchange of nearby loop inputs.
First undo the ambient alignment, then move the base time by half a period.
Only the alignment uses an arbitrarily small additive length margin. -/

@[expose] public section
namespace Finsler.NearJoinSwapHomotopy
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1FiberBase Finsler.H1LoopJoin
open Finsler.JoinDirectionComparison Finsler.JoinSplitHomotopy
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.CochainComparison
open Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable {n : ℕ} (F : ReversibleMetric n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  {ε : ℝ} (hε : 0 < ε)

def radius : ℝ := Classical.choose (JoinLengthComparison.exists_bounded_input_radius F a b ha.le hb.le hε)

theorem radius_pos : 0 < radius F a b ha hb hε :=
  (Classical.choose_spec (JoinLengthComparison.exists_bounded_input_radius F a b ha.le hb.le hε)).1

theorem radius_le_one : radius F a b ha hb hε ≤ 1 :=
  (Classical.choose_spec (JoinLengthComparison.exists_bounded_input_radius F a b ha.le hb.le hε)).2.1

def domain : Set (SphereLoop n × SphereLoop n) := {z |
  dist (basepoint z.1) (basepoint z.2) < radius F a b ha hb hε ∧
    SobolevLength.length F z.1 < a ∧ SobolevLength.length F z.2 < b}

def toNear : TopCat.of (domain F a b ha hb hε) ⟶ TopCat.of (nearPairs n) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, z.property.1.trans_le (radius_le_one F a b ha hb hε)⟩,
    continuous_subtype_val.subtype_mk _⟩

variable (C : ℝ) (hbudget : a + (b + ε) ≤ C)

include hbudget in
theorem comparison_bound (s : _root_.unitInterval) (z : domain F a b ha hb hε) :
    SobolevLength.length F (comparison half half.property.1 half.property.2
      (s, toNear F a b ha hb hε z)) < C := by
  have h := (Classical.choose_spec
    (JoinLengthComparison.exists_bounded_input_radius F a b ha.le hb.le hε)).2.2
    half half.property.1 half.property.2 (toNear F a b ha hb hε z) z.property.1
    z.property.2.1.le z.property.2.2.le s
  have hbnd : SobolevLength.length F z.val.1 + SobolevLength.length F z.val.2 + ε ≤ C := by
    linarith [z.property.2.1, z.property.2.2]
  exact h.2.trans_le hbnd

def first : TopCat.of (domain F a b ha hb hε) ⟶ lengthSpace F C :=
  TopCat.ofHom ⟨fun z => ⟨firstJoin half half.property.1 half.property.2 z.val.1 z.val.2, by
    have h := comparison_bound F a b ha hb hε C hbudget 1 z
    rw [ContinuousMap.Homotopy.apply_one] at h
    exact h⟩, by
    exact ((firstMap half half.property.1 half.property.2).continuous.comp
      (toNear F a b ha hb hε).hom.continuous).subtype_mk _⟩

def second : TopCat.of (domain F a b ha hb hε) ⟶ lengthSpace F C :=
  TopCat.ofHom ⟨fun z => ⟨secondJoin half half.property.1 half.property.2 z.val.1 z.val.2, by
    have h := comparison_bound F a b ha hb hε C hbudget 0 z
    rw [ContinuousMap.Homotopy.apply_zero] at h
    exact h⟩, by
    exact ((secondMap half half.property.1 half.property.2).continuous.comp
      (toNear F a b ha hb hε).hom.continuous).subtype_mk _⟩

def swappedFirst : TopCat.of (domain F a b ha hb hε) ⟶ lengthSpace F C :=
  second F a b ha hb hε C hbudget ≫ FilteredLoopTimeShift.shiftMap F C (1 / 2)

theorem swappedFirst_formula (z : domain F a b ha hb hε) :
    (swappedFirst F a b ha hb hε C hbudget z).val =
      firstJoin half half.property.1 half.property.2 z.val.2 z.val.1 := by
  exact HalfJoinTimeShift.half_join z.val.1 (align z.val.2 (point z.val.1))
    (basepoint_align z.val.2 (point z.val.1)).symm

def alignmentHomotopy : TopCat.Homotopy (second F a b ha hb hε C hbudget)
    (first F a b ha hb hε C hbudget) where
  toFun z := ⟨comparison half half.property.1 half.property.2
    (z.1, toNear F a b ha hb hε z.2), comparison_bound F a b ha hb hε C hbudget z.1 z.2⟩
  continuous_toFun := ((comparison half half.property.1 half.property.2).continuous.comp
    (continuous_fst.prodMk ((toNear F a b ha hb hε).hom.continuous.comp continuous_snd))).subtype_mk _
  map_zero_left z := Subtype.ext ((comparison half half.property.1 half.property.2).apply_zero
    (toNear F a b ha hb hε z))
  map_one_left z := Subtype.ext ((comparison half half.property.1 half.property.2).apply_one
    (toNear F a b ha hb hε z))

def homotopy : TopCat.Homotopy (first F a b ha hb hε C hbudget)
    (swappedFirst F a b ha hb hε C hbudget) :=
  (alignmentHomotopy F a b ha hb hε C hbudget).symm.trans
    ((FilteredLoopTimeShift.homotopy F C (1 / 2)).compContinuousMap
      (second F a b ha hb hε C hbudget).hom)

theorem homology_eq (q : ℕ) :
    HomologicalComplex.homologyMap (push (first F a b ha hb hε C hbudget)) q =
      HomologicalComplex.homologyMap (push (swappedFirst F a b ha hb hε C hbudget)) q :=
  ((homotopy F a b ha hb hε C hbudget).toSSet.chainComplexMap coeff).homologyMap_eq q

end
end Finsler.NearJoinSwapHomotopy
