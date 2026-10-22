module

public import Finsler.Topology.OriginalJoinComparison
public import Finsler.Topology.TimeShuffleComparison
public import Finsler.Analysis.SelfCutOscillation

/-! The original-join comparison is an actual homotopy inside a length
sublevel, with an actual singular-chain homotopy there. Input length bounds
are fixed before the common tube radius is selected. -/

@[expose] public section
namespace Finsler.FilteredOriginalJoin

open CategoryTheory AlgebraicTopology HomologicalComplex
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.VariableJoinContinuity Finsler.JoinSplitHomotopy Finsler.JoinDirectionComparison
open Finsler.SobolevLength Finsler.SelfCutOscillation
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
  {ε : ℝ} (hε : 0 < ε)

def radius : ℝ := (OriginalJoinComparison.exists_length_radius F p q hp hq hε).choose

theorem radius_spec : 0 < radius F p q hp hq hε ∧ radius F p q hp hq hε ≤ 1 ∧
    ∀ (a : Splits) (z : nearPairs n),
      dist (basepoint z.val.1) (basepoint z.val.2) < radius F p q hp hq hε →
      length F z.val.1 ≤ p → length F z.val.2 ≤ q →
      ∀ s : _root_.unitInterval,
        length F (OriginalJoinComparison.comparisonToHalf a (s, z)) <
          length F z.val.1 + length F z.val.2 + ε :=
  (OriginalJoinComparison.exists_length_radius F p q hp hq hε).choose_spec

def domain : Set (nearPairs n) := {z |
  dist (basepoint z.val.1) (basepoint z.val.2) < radius F p q hp hq hε ∧
    length F z.val.1 ≤ p ∧ length F z.val.2 ≤ q}

theorem image_length (a : Splits) (z : domain F p q hp hq hε) (s : _root_.unitInterval) :
    length F (OriginalJoinComparison.comparisonToHalf a (s, z.val)) < p + q + ε := by
  have h := (radius_spec F p q hp hq hε).2.2 a z.val z.property.1
    z.property.2.1 z.property.2.2 s
  linarith [z.property.2.1, z.property.2.2]

def atTime (a : Splits) (s : _root_.unitInterval) :
    C(domain F p q hp hq hε, short F (p + q + ε)) :=
  ⟨fun z => ⟨OriginalJoinComparison.comparisonToHalf a (s, z.val),
      image_length F p q hp hq hε a z s⟩, by
    have h : Continuous (fun z : domain F p q hp hq hε =>
        OriginalJoinComparison.comparisonToHalf a (s, z.val)) :=
      (OriginalJoinComparison.comparisonToHalf a).continuous.comp
        (continuous_const.prodMk continuous_subtype_val)
    exact h.subtype_mk _⟩

def homotopy (a : Splits) :
    (atTime F p q hp hq hε a 0).Homotopy (atTime F p q hp hq hε a 1) where
  toFun z := ⟨OriginalJoinComparison.comparisonToHalf a (z.1, z.2.val),
    image_length F p q hp hq hε a z.2 z.1⟩
  continuous_toFun := by
    have h : Continuous (fun z : _root_.unitInterval × domain F p q hp hq hε =>
        OriginalJoinComparison.comparisonToHalf a (z.1, z.2.val)) :=
      (OriginalJoinComparison.comparisonToHalf a).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_mk _
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem zero_formula (a : Splits) (z : domain F p q hp hq hε) :
    (atTime F p q hp hq hε a 0 z).val =
      secondJoin a a.property.1 a.property.2 z.val.val.1 z.val.val.2 :=
  (OriginalJoinComparison.comparisonToHalf a).map_zero_left z.val

theorem one_formula (a : Splits) (z : domain F p q hp hq hε) :
    (atTime F p q hp hq hε a 1 z).val =
      firstJoin half half.property.1 half.property.2 z.val.val.1 z.val.val.2 :=
  (OriginalJoinComparison.comparisonToHalf a).map_one_left z.val

def topHomotopy (a : Splits) :
    TopCat.Homotopy (TopCat.ofHom (atTime F p q hp hq hε a 0))
      (TopCat.ofHom (atTime F p q hp hq hε a 1)) where
  toFun z := homotopy F p q hp hq hε a z
  continuous_toFun := (homotopy F p q hp hq hε a).continuous
  map_zero_left z := (homotopy F p q hp hq hε a).map_zero_left z
  map_one_left z := (homotopy F p q hp hq hε a).map_one_left z

def chainHomotopy (a : Splits) :
    Homotopy (SupportedCapNaturality.push (TopCat.ofHom (atTime F p q hp hq hε a 0)))
      (SupportedCapNaturality.push (TopCat.ofHom (atTime F p q hp hq hε a 1))) :=
  (topHomotopy F p q hp hq hε a).toSSet.chainComplexMap coeff

theorem homology_eq (a : Splits) (k : ℕ) :
    homologyMap (SupportedCapNaturality.push (TopCat.ofHom (atTime F p q hp hq hε a 0))) k =
      homologyMap (SupportedCapNaturality.push (TopCat.ofHom (atTime F p q hp hq hε a 1))) k :=
  (chainHomotopy F p q hp hq hε a).homologyMap_eq k

end
end Finsler.FilteredOriginalJoin
