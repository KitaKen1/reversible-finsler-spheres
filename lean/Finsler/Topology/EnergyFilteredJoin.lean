module

public import Finsler.Topology.SupportedFilteredJoinComparison
public import Finsler.Topology.LengthEnergyMaps

/-! The original energy-cut inputs map continuously to bounded length
inputs. The actual original-join comparison is carried back to the original
output energy cut by arclength normalization, with explicit endpoints. -/

@[expose] public section
namespace Finsler.EnergyFilteredJoin

open CategoryTheory AlgebraicTopology HomologicalComplex SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SobolevLength Finsler.SobolevReflectionAction Finsler.SobolevEnergy
open Finsler.SupportedFilteredJoinComparison Finsler.CompactH1Alignment
open Finsler.VariableJoinContinuity Finsler.JoinDirectionComparison
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {n : ℕ} (F : ReversibleMetric n)

theorem length_le_sqrt_energy (u : SphereLoop n) :
    length F u ≤ Real.sqrt (energy F u) := by
  nlinarith [length_sq_le_energy F u, length_nonneg F u, Real.sqrt_nonneg (energy F u),
    Real.sq_sqrt (energy_nonneg F u)]

def energyToLength (p : ℝ) : TopCat.of (energyCut F p) ⟶ lengthSpace F p :=
  TopCat.ofHom ⟨fun u => ⟨u.val, ((length_le_sqrt_energy F u.val).trans_lt u.property).le⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem energyToLength_factor (p : ℝ) :
    energyToLength F p ≫ SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
      {u | length F u ≤ p} =
      SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (energyCut F p) := by
  ext u : 1
  rfl

def inputSpace (p q : ℝ) : TopCat.{0} := TopCat.of (energyCut F p) ⊗ TopCat.of (energyCut F q)

def inputMap (p q : ℝ) : inputSpace F p q ⟶ lengthSpace F p ⊗ lengthSpace F q :=
  TopCat.ofHom ⟨fun z => (energyToLength F p z.1, energyToLength F q z.2),
    ((energyToLength F p).hom.continuous.comp continuous_fst).prodMk
      ((energyToLength F q).hom.continuous.comp continuous_snd)⟩

theorem inputMap_factor (p q : ℝ) :
    inputMap F p q ≫ SupportedFilteredJoinComparison.inputMap F p q =
      TopCat.ofHom ⟨fun z => (z.1.val, z.2.val),
        (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)⟩ := by
  ext z : 1
  rfl

variable (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) {ε : ℝ} (hε : 0 < ε)

include hp hq hε in
theorem output_positive : 0 < p + q + ε := by linarith

def domain : Set (inputSpace F p q) := {z |
  dist (basepoint z.1.val) (basepoint z.2.val) < FilteredOriginalJoin.radius F p q hp hq hε}

def toFlat : TopCat.of (domain F p q hp hq hε) ⟶
    TopCat.of (JoinRectangleComparison.flatDomain F p q hp hq hε) :=
  TopCat.ofHom ⟨fun z => ⟨(z.val.1.val, z.val.2.val), z.property,
    ((length_le_sqrt_energy F z.val.1.val).trans_lt z.val.1.property).le,
    ((length_le_sqrt_energy F z.val.2.val).trans_lt z.val.2.property).le⟩,
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

def atTime (a : Splits) (s : _root_.unitInterval) :
    TopCat.of (domain F p q hp hq hε) ⟶ TopCat.of (energyCut F (p + q + ε)) :=
  toFlat F p q hp hq hε ≫ TopCat.ofHom (JoinRectangleComparison.toDomain F p q hp hq hε) ≫
    TopCat.ofHom (FilteredOriginalJoin.atTime F p q hp hq hε a s) ≫
      LengthEnergyMaps.lengthToEnergy F (output_positive p q hp hq hε)

def topHomotopy (a : Splits) :
    TopCat.Homotopy (atTime F p q hp hq hε a 0) (atTime F p q hp hq hε a 1) where
  toFun z := LengthEnergyMaps.lengthToEnergy F (output_positive p q hp hq hε)
    (FilteredOriginalJoin.homotopy F p q hp hq hε a
      (z.1, JoinRectangleComparison.toDomain F p q hp hq hε (toFlat F p q hp hq hε z.2)))
  continuous_toFun := (LengthEnergyMaps.lengthToEnergy F (output_positive p q hp hq hε)).hom.continuous.comp
    ((FilteredOriginalJoin.homotopy F p q hp hq hε a).continuous.comp
      (continuous_fst.prodMk
        ((JoinRectangleComparison.toDomain F p q hp hq hε).continuous.comp
          ((toFlat F p q hp hq hε).hom.continuous.comp continuous_snd))))
  map_zero_left _ := rfl
  map_one_left _ := rfl

def chainHomotopy (a : Splits) :
    Homotopy (push (atTime F p q hp hq hε a 0)) (push (atTime F p q hp hq hε a 1)) :=
  (topHomotopy F p q hp hq hε a).toSSet.chainComplexMap coeff

theorem zero_formula (a : Splits) (z : domain F p q hp hq hε) :
    (atTime F p q hp hq hε a 0 z).val =
      LengthEnergyMaps.normalizer F
        (secondJoin a a.property.1 a.property.2 z.val.1.val z.val.2.val) :=
  congrArg (LengthEnergyMaps.normalizer F)
    (FilteredOriginalJoin.zero_formula F p q hp hq hε a
      (JoinRectangleComparison.toDomain F p q hp hq hε (toFlat F p q hp hq hε z)))

theorem one_formula (a : Splits) (z : domain F p q hp hq hε) :
    (atTime F p q hp hq hε a 1 z).val =
      LengthEnergyMaps.normalizer F
        (firstJoin JoinSplitHomotopy.half JoinSplitHomotopy.half.property.1
          JoinSplitHomotopy.half.property.2 z.val.1.val z.val.2.val) :=
  congrArg (LengthEnergyMaps.normalizer F)
    (FilteredOriginalJoin.one_formula F p q hp hq hε a
      (JoinRectangleComparison.toDomain F p q hp hq hε (toFlat F p q hp hq hε z)))

theorem homology_eq (a : Splits) (s : ℕ) :
    homologyMap (push (atTime F p q hp hq hε a 0)) s =
      homologyMap (push (atTime F p q hp hq hε a 1)) s :=
  (chainHomotopy F p q hp hq hε a).homologyMap_eq s

end
end Finsler.EnergyFilteredJoin
