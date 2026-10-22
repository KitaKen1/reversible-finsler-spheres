module

public import Finsler.Geometry.PolygonModel
public import Finsler.Analysis.SelfCutOscillation
public import Finsler.Topology.DiagonalCohomology

/-! Actual arclength normalization compares the original strong-H1 length
and energy sublevels. Its homotopy, class action and constant loops are explicit. -/

@[expose] public section
namespace Finsler.LengthEnergyMaps

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.NormalizationHomotopy Finsler.SobolevLength Finsler.SobolevReflectionAction
open Finsler.SelfCutOscillation
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {n : ℕ}

theorem continuous_normalization (F : ReversibleMetric n) :
    Continuous (fun z : ClosedInterval × SphereLoop n => normLoop F (z.1.val, z.2)) :=
  (NormalizationContinuity.normLoop_continuousOn F).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun z => ⟨z.1.property, Set.mem_univ _⟩)

def normalizer (F : ReversibleMetric n) : TopCat.of (SphereLoop n) ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom ⟨fun u => normLoop F (1, u), by
    have hc : Continuous (fun u : SphereLoop n => ((1 : ClosedInterval), u)) :=
      continuous_const.prodMk continuous_id
    exact ((continuous_normalization F).comp hc).congr (fun _ => rfl)⟩

def normalizationHomotopy (F : ReversibleMetric n) :
    TopCat.Homotopy (𝟙 (TopCat.of (SphereLoop n))) (normalizer F) where
  toFun z := normLoop F (z.1.val, z.2)
  continuous_toFun := continuous_normalization F
  map_zero_left u := normLoop_zero F u
  map_one_left _ := rfl

theorem normalizer_cohomology (F : ReversibleMetric n) (p : ℕ)
    (a : cohomologyZMod2 (TopCat.of (SphereLoop n)) p) :
    (cohPullback (normalizer F) p).hom a = a := by
  have h := DiagonalCohomology.homotopy_pullback (normalizationHomotopy F) p a
  rw [DiagonalCohomology.pullback_id] at h
  exact h.symm

theorem normalizer_length (F : ReversibleMetric n) (u : SphereLoop n) :
    length F (normalizer F u) = length F u := length_normLoop F _

theorem normalizer_energy (F : ReversibleMetric n) (u : SphereLoop n) :
    SobolevEnergy.energy F (normalizer F u) ≤ length F u ^ 2 := by
  change SobolevEnergy.energy F (normLoop F (1, u)) ≤ length F u ^ 2
  have h := energy_normLoop_le F (s := 1) (by constructor <;> norm_num) u
  simpa only [sub_self, zero_mul, one_mul, zero_add] using h

theorem normalizer_constant (F : ReversibleMetric n) (x : Sphere n) :
    normalizer F (constantSphereLoop x) = constantSphereLoop x := by
  have he := SobolevEnergy.energy_constantSphereLoop F x
  have hsq := length_sq_le_energy F (constantSphereLoop x)
  have hzero : length F (constantSphereLoop x) = 0 := by nlinarith [length_nonneg F (constantSphereLoop x)]
  exact normLoop_of_length_eq_zero F (p := (1, constantSphereLoop x)) hzero

def lengthToEnergy (F : ReversibleMetric n) {L : ℝ} (hL : 0 < L) :
    TopCat.of (short F L) ⟶ TopCat.of (energyCut F L) :=
  TopCat.ofHom ⟨fun u => ⟨normalizer F u.val, (Real.sqrt_lt' hL).mpr
    (PolygonModel.energy_normLoop_one_lt F hL u.property)⟩,
    ((normalizer F).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem lengthToEnergy_factor (F : ReversibleMetric n) {L : ℝ} (hL : 0 < L) :
    SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L) ≫ normalizer F =
      lengthToEnergy F hL ≫ SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (energyCut F L) := by
  ext u : 1
  rfl

end
end Finsler.LengthEnergyMaps
