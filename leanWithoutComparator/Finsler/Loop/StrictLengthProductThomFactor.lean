module

public import Finsler.Loop.StrictLengthProductCompatibility
public import Finsler.Loop.LengthProductNormalizationGeometry

/-! The transported length product is the genuine diagonal Thom cut
on the original length-pair space followed by an actual normalized
near join into the same strict length target. -/

@[expose] public section
namespace Finsler.StrictLengthProductThomFactor

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.CompactH1Alignment
open Finsler.StrictLengthEnergyBridge Finsler.StrictLengthLoopProduct
open Finsler.LengthProductNormalizationGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)

def tube := near F p q (H1NearJoin.radius F hq hε)

theorem tube_open : IsOpen (tube F p hq hε) := near_open F p q _

theorem diagonal_in_tube (z : pairSpace F p q)
    (hz : leftEvaluation F p q z = rightEvaluation F p q z) : z ∈ tube F p hq hε := by
  have he := congrArg Subtype.val hz
  change basepoint z.1.val = basepoint z.2.val at he
  change dist (basepoint z.1.val) (basepoint z.2.val) < H1NearJoin.radius F hq hε
  rw [he, dist_self]
  exact (H1NearJoin.radius_spec F hq hε).1

theorem maps_to_energy_tube : Set.MapsTo (pairMap F p q) (tube F p hq hε) (H1NearJoin.tube F p hq hε) := by
  intro z hz
  change dist (basepoint (toEnergy F q z.2).val) (basepoint (toEnergy F p z.1).val) < H1NearJoin.radius F hq hε
  rw [toEnergy_basepoint, toEnergy_basepoint, dist_comm]
  exact hz

def toEnergyNear := restriction (pairMap F p q) (tube F p hq hε) (H1NearJoin.tube F p hq hε)
  (maps_to_energy_tube F p hq hε)

def thomOperation (hn : 1 ≤ n) := DiagonalCutNaturality.operation hn
  (leftEvaluation F p q) (rightEvaluation F p q) (tube F p hq hε)
  (tube_open F p hq hε) (diagonal_in_tube F p hq hε)

theorem thom_naturality (hn : 1 ≤ n) (k : ℕ) :
    HomologicalComplex.homologyMap (push (pairMap F p q)) (n + k) ≫
      (FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k =
    (thomOperation F p hq hε hn).homology k ≫
      HomologicalComplex.homologyMap (push (toEnergyNear F p hq hε)) k := by
  have hx : ∀ z, (pairMap F p q ≫ FilteredLoopProduct.leftEvaluation F p q) z =
      (pairMap F p q ≫ FilteredLoopProduct.rightEvaluation F p q) z → z ∈ tube F p hq hε := by
    rw [pairMap_left, pairMap_right]
    exact diagonal_in_tube F p hq hε
  have he := DiagonalCutNaturality.homology_naturality hn (pairMap F p q)
    (FilteredLoopProduct.leftEvaluation F p q) (FilteredLoopProduct.rightEvaluation F p q)
    (tube F p hq hε) (H1NearJoin.tube F p hq hε) (tube_open F p hq hε)
    (FilteredLoopProduct.tube_open F p hq hε) hx (FilteredLoopProduct.diagonal_in_tube F p hq hε)
    (maps_to_energy_tube F p hq hε) k
  have henergy : (DiagonalCutNaturality.operation hn
      (FilteredLoopProduct.leftEvaluation F p q) (FilteredLoopProduct.rightEvaluation F p q)
      (H1NearJoin.tube F p hq hε) (FilteredLoopProduct.tube_open F p hq hε)
      (FilteredLoopProduct.diagonal_in_tube F p hq hε)).homology k =
      (FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro i
    rfl
  rw [henergy] at he
  simpa only [pairMap_left, pairMap_right, thomOperation, toEnergyNear] using he

variable (hp : 0 < p)

def joinMap : TopCat.of (tube F p hq hε) ⟶ lengthSpace F (p + (q + ε)) :=
  toEnergyNear F p hq hε ≫ NearJoinChains.nearJoinMorphism F hp hq hε ≫
    toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε))

def timing : VariableJoinContinuity.Splits :=
  ⟨p / (p + (q + ε)), div_pos hp (add_pos hp (add_pos hq hε)),
    (div_lt_one (add_pos hp (add_pos hq hε))).mpr (by linarith)⟩

theorem joinMap_formula (z : tube F p hq hε) :
    (joinMap F p hq hε hp z).val = JoinDirectionComparison.secondJoin
      (timing p hq hε hp) (timing p hq hε hp).property.1 (timing p hq hε hp).property.2
      (LengthEnergyMaps.normalizer F z.val.1.val) (LengthEnergyMaps.normalizer F z.val.2.val) := rfl

theorem positive_homology_factor (hn : 1 ≤ n) (k : ℕ) :
    (positiveOperation F hn hp hq hε).homology k =
    (thomOperation F p hq hε hn).homology k ≫ HomologicalComplex.homologyMap (push (joinMap F p hq hε hp)) k := by
  rw [positive_homology, FilteredLoopProductHomology.product_homology_factor]
  have hj : push (joinMap F p hq hε hp) = push (toEnergyNear F p hq hε) ≫
      NearJoinChains.joinChainMap F hp hq hε ≫
      push (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε))) := by
    rw [joinMap, push_comp, push_comp]
    rfl
  rw [hj, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  simp only [← Category.assoc]
  rw [thom_naturality F p hq hε hn k]

theorem product_factor (hn : 1 ≤ n) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    positiveProduct F hn hp hq hε i j k h x y =
    (HomologicalComplex.homologyMap (push (joinMap F p hq hε hp)) k).hom
      (((thomOperation F p hq hε hn).homology k).hom
        (FilteredBilinearLoopProduct.cross (lengthSpace F p) (lengthSpace F q) i j (n + k) h x y)) := by
  rw [StrictLengthProductCompatibility.positive_chain_apply, positive_homology_factor]
  rfl

end
end Finsler.StrictLengthProductThomFactor
