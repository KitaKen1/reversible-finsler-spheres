module

public import Finsler.Topology.EnergyFilteredJoin

/-! Actual strong-H1 maps and sublevel homotopies between strict
length bounds and positive energy levels. Arclength normalization
preserves the basepoint; neither direction is an assumed inclusion. -/

@[expose] public section
namespace Finsler.StrictLengthEnergyBridge

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.BorelLoop
open Finsler.SobolevLength Finsler.NormalizationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {n : ℕ} (F : ReversibleMetric n) (a : ℝ)

abbrev lengthSpace : TopCat.{0} := TopCat.of (SelfCutOscillation.short F a)
abbrev energySpace : TopCat.{0} := TopCat.of (lev F a)

theorem level_pos (u : SelfCutOscillation.short F a) : 0 < a :=
  (length_nonneg F u.val).trans_lt u.property

theorem short_empty (ha : a ≤ 0) : IsEmpty (SelfCutOscillation.short F a) :=
  ⟨fun u => (not_lt_of_ge ha (level_pos F a u)).elim⟩

def toEnergy : lengthSpace F a ⟶ energySpace F a :=
  TopCat.ofHom ⟨fun u => ⟨LengthEnergyMaps.normalizer F u.val,
    (Birkhoff.mem_lev_iff (level_pos F a u) _).mpr
      (PolygonModel.energy_normLoop_one_lt F (level_pos F a u) u.property)⟩,
    ((LengthEnergyMaps.normalizer F).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def toLength (ha : 0 < a) : energySpace F a ⟶ lengthSpace F a :=
  TopCat.ofHom ⟨fun u => ⟨u.val, PolygonModel.length_lt_of_energy_lt F ha
    ((Birkhoff.mem_lev_iff ha u.val).mp u.property)⟩, continuous_subtype_val.subtype_mk _⟩

theorem toEnergy_source : toEnergy F a ≫ SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (lev F a) =
    SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F a) ≫
      LengthEnergyMaps.normalizer F := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  rfl

theorem toLength_source (ha : 0 < a) : toLength F a ha ≫
    SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F a) =
      SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (lev F a) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  rfl

theorem normLoop_basepoint (s : ℝ) (u : SphereLoop n) :
    CompactH1Alignment.basepoint (normLoop F (s, u)) = CompactH1Alignment.basepoint u :=
  representative_normLoop_zero F (s, u)

theorem normLoop_point (s : ℝ) (u : SphereLoop n) :
    H1FiberBase.point (normLoop F (s, u)) = H1FiberBase.point u := by
  apply Subtype.ext
  exact normLoop_basepoint F s u

theorem toEnergy_basepoint (u : lengthSpace F a) :
    CompactH1Alignment.basepoint (toEnergy F a u).val = CompactH1Alignment.basepoint u.val :=
  normLoop_basepoint F 1 u.val

def shortHomotopy (ha : 0 < a) :
    TopCat.Homotopy (𝟙 (lengthSpace F a)) (toEnergy F a ≫ toLength F a ha) where
  toFun z := ⟨normLoop F (z.1.val, z.2.val), PolygonModel.length_normLoop_lt F z.2.property⟩
  continuous_toFun := ((LengthEnergyMaps.continuous_normalization F).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left u := Subtype.ext (normLoop_zero F u.val)
  map_one_left _ := rfl

def energyHomotopy (ha : 0 < a) :
    TopCat.Homotopy (𝟙 (energySpace F a)) (toLength F a ha ≫ toEnergy F a) where
  toFun z := ⟨normLoop F (z.1.val, z.2.val), (Birkhoff.mem_lev_iff ha _).mpr
    (PolygonModel.energy_normLoop_lt F z.1.property ((Birkhoff.mem_lev_iff ha _).mp z.2.property))⟩
  continuous_toFun := ((LengthEnergyMaps.continuous_normalization F).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left u := Subtype.ext (normLoop_zero F u.val)
  map_one_left _ := rfl

theorem short_homology_inverse (ha : 0 < a) (q : ℕ) :
    HomologicalComplex.homologyMap (push (toEnergy F a)) q ≫
      HomologicalComplex.homologyMap (push (toLength F a ha)) q = 𝟙 ((chains (lengthSpace F a)).homology q) := by
  have he := ((shortHomotopy F a ha).toSSet.chainComplexMap coeff).homologyMap_eq q
  change HomologicalComplex.homologyMap (push (𝟙 (lengthSpace F a))) q =
    HomologicalComplex.homologyMap (push (toEnergy F a ≫ toLength F a ha)) q at he
  have hid : push (𝟙 (lengthSpace F a)) = 𝟙 (chains (lengthSpace F a)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (lengthSpace F a))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.homologyMap_id, push_comp, HomologicalComplex.homologyMap_comp] at he
  exact he.symm

theorem energy_homology_inverse (ha : 0 < a) (q : ℕ) :
    HomologicalComplex.homologyMap (push (toLength F a ha)) q ≫
      HomologicalComplex.homologyMap (push (toEnergy F a)) q = 𝟙 ((chains (energySpace F a)).homology q) := by
  have he := ((energyHomotopy F a ha).toSSet.chainComplexMap coeff).homologyMap_eq q
  change HomologicalComplex.homologyMap (push (𝟙 (energySpace F a))) q =
    HomologicalComplex.homologyMap (push (toLength F a ha ≫ toEnergy F a)) q at he
  have hid : push (𝟙 (energySpace F a)) = 𝟙 (chains (energySpace F a)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (energySpace F a))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.homologyMap_id, push_comp, HomologicalComplex.homologyMap_comp] at he
  exact he.symm

def homologyIso (ha : 0 < a) (q : ℕ) :
    (chains (lengthSpace F a)).homology q ≅ (chains (energySpace F a)).homology q where
  hom := HomologicalComplex.homologyMap (push (toEnergy F a)) q
  inv := HomologicalComplex.homologyMap (push (toLength F a ha)) q
  hom_inv_id := short_homology_inverse F a ha q
  inv_hom_id := energy_homology_inverse F a ha q

end
end Finsler.StrictLengthEnergyBridge
