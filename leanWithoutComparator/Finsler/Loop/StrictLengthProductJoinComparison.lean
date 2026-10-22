module

public import Finsler.Loop.StrictLengthProductThomFactor
public import Finsler.Topology.FilteredOriginalJoin

/-! The transported energy join is homotopic to the original half-time
first join in exactly the same strict length target. A common positive
tube is chosen using the pre-existing uniform length comparison. -/

@[expose] public section
namespace Finsler.StrictLengthProductJoinComparison

open CategoryTheory AlgebraicTopology
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.CompactH1Alignment Finsler.SobolevLength
open Finsler.StrictLengthEnergyBridge Finsler.StrictLengthLoopProduct
open Finsler.LengthProductNormalizationGeometry
open Finsler.JoinDirectionComparison Finsler.JoinSplitHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
  {ε : ℝ} (hε : 0 < ε)

def radius : ℝ := min (H1NearJoin.radius F hq hε)
  (FilteredOriginalJoin.radius F p q hp.le hq.le hε)

theorem radius_pos : 0 < radius F p q hp hq hε :=
  lt_min (H1NearJoin.radius_spec F hq hε).1
    (FilteredOriginalJoin.radius_spec F p q hp.le hq.le hε).1

def commonTube := near F p q (radius F p q hp hq hε)

theorem commonTube_open : IsOpen (commonTube F p q hp hq hε) := near_open F p q _

theorem commonTube_sub_product : commonTube F p q hp hq hε ⊆
    StrictLengthProductThomFactor.tube F p hq hε := by
  intro z hz
  change dist (basepoint z.1.val) (basepoint z.2.val) < min _ _ at hz
  change dist (basepoint z.1.val) (basepoint z.2.val) < _
  exact lt_of_lt_of_le hz (min_le_left _ _)

def toProductTube := restriction (𝟙 (pairSpace F p q)) (commonTube F p q hp hq hε)
  (StrictLengthProductThomFactor.tube F p hq hε) (commonTube_sub_product F p q hp hq hε)

def toDomain : TopCat.of (commonTube F p q hp hq hε) ⟶
    TopCat.of (FilteredOriginalJoin.domain F p q hp.le hq.le hε) := TopCat.ofHom
  ⟨fun z => ⟨⟨(z.val.1.val, z.val.2.val),
    (lt_of_lt_of_le (lt_of_lt_of_le z.property (min_le_right _ _))
      (FilteredOriginalJoin.radius_spec F p q hp.le hq.le hε).2.1)⟩,
    lt_of_lt_of_le z.property (min_le_right _ _), z.val.1.property.le, z.val.2.property.le⟩,
    by
      have hc : Continuous (fun z : commonTube F p q hp hq hε => (z.val.1.val, z.val.2.val)) :=
        ((continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val).prodMk
          ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val)
      exact (hc.subtype_mk _).subtype_mk _⟩

def outputReassoc : lengthSpace F (p + q + ε) ⟶ lengthSpace F (p + (q + ε)) := TopCat.ofHom
  ⟨fun u => ⟨u.val, lt_of_lt_of_eq u.property (add_assoc p q ε)⟩,
    continuous_subtype_val.subtype_mk _⟩

def rawJoin : TopCat.of (commonTube F p q hp hq hε) ⟶ lengthSpace F (p + (q + ε)) :=
  toDomain F p q hp hq hε ≫
    TopCat.ofHom (FilteredOriginalJoin.atTime F p q hp.le hq.le hε half 1) ≫ outputReassoc F p q

theorem rawJoin_formula (z : commonTube F p q hp hq hε) :
    (rawJoin F p q hp hq hε z).val = firstJoin half half.property.1 half.property.2
      z.val.1.val z.val.2.val :=
  FilteredOriginalJoin.one_formula F p q hp.le hq.le hε half (toDomain F p q hp hq hε z)

def normalizedRawJoin : TopCat.of (commonTube F p q hp hq hε) ⟶ lengthSpace F (p + (q + ε)) :=
  nearAtTime F p q hp hq (radius F p q hp hq hε) 1 ≫ rawJoin F p q hp hq hε

def normalizedComparison : TopCat.Homotopy
    (toProductTube F p q hp hq hε ≫ StrictLengthProductThomFactor.joinMap F p hq hε hp)
    (normalizedRawJoin F p q hp hq hε) where
  toFun z := outputReassoc F p q
    ((FilteredOriginalJoin.homotopy F p q hp.le hq.le hε (StrictLengthProductThomFactor.timing p hq hε hp))
      (z.1, toDomain F p q hp hq hε (nearAtTime F p q hp hq (radius F p q hp hq hε) 1 z.2)))
  continuous_toFun := by
    exact (outputReassoc F p q).hom.continuous.comp
      ((FilteredOriginalJoin.homotopy F p q hp.le hq.le hε (StrictLengthProductThomFactor.timing p hq hε hp)).continuous.comp
        (continuous_fst.prodMk ((toDomain F p q hp hq hε).hom.continuous.comp
          ((nearAtTime F p q hp hq (radius F p q hp hq hε) 1).hom.continuous.comp continuous_snd))))
  map_zero_left z := by
    apply Subtype.ext
    change (FilteredOriginalJoin.atTime F p q hp.le hq.le hε
      (StrictLengthProductThomFactor.timing p hq hε hp) 0
      (toDomain F p q hp hq hε (nearAtTime F p q hp hq (radius F p q hp hq hε) 1 z))).val = _
    rw [FilteredOriginalJoin.zero_formula]
    exact (StrictLengthProductThomFactor.joinMap_formula F p hq hε hp (toProductTube F p q hp hq hε z)).symm
  map_one_left z := by
    apply Subtype.ext
    change (FilteredOriginalJoin.atTime F p q hp.le hq.le hε
      (StrictLengthProductThomFactor.timing p hq hε hp) 1
      (toDomain F p q hp hq hε (nearAtTime F p q hp hq (radius F p q hp hq hε) 1 z))).val = _
    exact (FilteredOriginalJoin.one_formula F p q hp.le hq.le hε
      (StrictLengthProductThomFactor.timing p hq hε hp) _).trans
      (rawJoin_formula F p q hp hq hε (nearAtTime F p q hp hq (radius F p q hp hq hε) 1 z)).symm

def rawNormalization : TopCat.Homotopy (rawJoin F p q hp hq hε) (normalizedRawJoin F p q hp hq hε) where
  toFun z := rawJoin F p q hp hq hε (nearHomotopy F p q hp hq (radius F p q hp hq hε) z)
  continuous_toFun := (rawJoin F p q hp hq hε).hom.continuous.comp
    (nearHomotopy F p q hp hq (radius F p q hp hq hε)).continuous
  map_zero_left z := by
    exact congrArg (fun w : commonTube F p q hp hq hε => rawJoin F p q hp hq hε w)
      ((nearHomotopy F p q hp hq (radius F p q hp hq hε)).map_zero_left z)
  map_one_left z := by rfl

def homotopy : TopCat.Homotopy
    (toProductTube F p q hp hq hε ≫ StrictLengthProductThomFactor.joinMap F p hq hε hp)
    (rawJoin F p q hp hq hε) :=
  (normalizedComparison F p q hp hq hε).trans (rawNormalization F p q hp hq hε).symm

def chainHomotopy : Homotopy
    (push (toProductTube F p q hp hq hε ≫ StrictLengthProductThomFactor.joinMap F p hq hε hp))
    (push (rawJoin F p q hp hq hε)) :=
  (homotopy F p q hp hq hε).toSSet.chainComplexMap coeff

theorem homology_eq (k : ℕ) :
    HomologicalComplex.homologyMap (push (toProductTube F p q hp hq hε)) k ≫
      HomologicalComplex.homologyMap (push (StrictLengthProductThomFactor.joinMap F p hq hε hp)) k =
    HomologicalComplex.homologyMap (push (rawJoin F p q hp hq hε)) k := by
  rw [← HomologicalComplex.homologyMap_comp, ← push_comp]
  exact (chainHomotopy F p q hp hq hε).homologyMap_eq k

end
end Finsler.StrictLengthProductJoinComparison
