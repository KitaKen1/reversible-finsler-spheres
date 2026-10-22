module

public import Finsler.Analysis.IntervalH1ReflectionAction
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Analysis.Normed.Module.Basic

/-! Genuine continuous circle representatives of actual periodic weak H¹ data.
The interval representative is descended through the standard additive circle.
Its norm and joint continuity are certified from the actual H¹ graph. Shifted
representatives are candidates for H¹ rotation; no shifted weak derivative,
H¹ rotation action, energy invariance or H¹ circle identification is asserted. -/

@[expose] public section

namespace Finsler.SobolevCircleRepresentative

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevReverse Set
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

abbrev Circle := AddCircle (1 : ℝ)

def circlePoint (x : Circle) : ClosedInterval :=
  ⟨(AddCircle.equivIco (1 : ℝ) 0 x : ℝ), by
    have h := (AddCircle.equivIco (1 : ℝ) 0 x).property
    simpa only [zero_add] using Ico_subset_Icc_self h⟩

theorem circlePoint_coe (x : Circle) : ((circlePoint x : ℝ) : Circle) = x :=
  AddCircle.coe_equivIco

theorem periodic_endpoint_eq {n : ℕ} (u : periodicSubmodule n) :
    continuousRepresentative (u : Space n) 0 = continuousRepresentative (u : Space n) 1 :=
  (mem_periodicSubmodule_iff (u : Space n) |>.mp u.property).symm

def circleMap {n : ℕ} (u : periodicSubmodule n) : C(Circle, Ambient n) :=
  ⟨AddCircle.liftIco (1 : ℝ) 0 (continuousRepresentative (u : Space n)),
    AddCircle.liftIco_zero_continuous (periodic_endpoint_eq u)
      (continuousRepresentative_continuousOn (u : Space n))⟩

theorem circleMap_apply {n : ℕ} (u : periodicSubmodule n) (x : Circle) :
    circleMap u x = continuousRepresentative (u : Space n) (circlePoint x) := rfl

theorem circleMap_coe {n : ℕ} (u : periodicSubmodule n) {t : ℝ} (ht : t ∈ Icc 0 1) :
    circleMap u (t : Circle) = continuousRepresentative (u : Space n) t := by
  by_cases he : t = 1
  · subst t
    change AddCircle.liftIco (1 : ℝ) 0 (continuousRepresentative (u : Space n)) ((1 : ℝ) : Circle) = _
    rw [AddCircle.coe_period]
    have hz := AddCircle.liftIco_zero_coe_apply (p := (1 : ℝ))
      (f := continuousRepresentative (u : Space n)) (x := 0) (by norm_num)
    rw [AddCircle.coe_zero] at hz
    exact hz.trans (periodic_endpoint_eq u)
  · have hlt : t < (1 : ℝ) := by
      rcases lt_or_eq_of_le ht.2 with hlt | heq
      · exact hlt
      · exact False.elim (he heq)
    exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, hlt⟩

theorem circleMap_norm_le {n : ℕ} (u : periodicSubmodule n) :
    ‖circleMap u‖ ≤ 2 * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 2 * ‖u‖)).mpr
  intro x
  rw [circleMap_apply]
  exact continuousRepresentative_norm_le_two (u : Space n) (circlePoint x).property

def circleLinear (n : ℕ) : periodicSubmodule n →ₗ[ℝ] C(Circle, Ambient n) where
  toFun := circleMap
  map_add' u v := by
    apply ContinuousMap.ext
    intro x
    change continuousRepresentative ((u : Space n) + (v : Space n)) (circlePoint x) = _
    exact continuousRepresentative_add (u : Space n) (v : Space n) (circlePoint x).property
  map_smul' a u := by
    apply ContinuousMap.ext
    intro x
    change continuousRepresentative (a • (u : Space n)) (circlePoint x) = _
    exact continuousRepresentative_smul a (u : Space n) (circlePoint x).property

def circleL (n : ℕ) : periodicSubmodule n →L[ℝ] C(Circle, Ambient n) :=
  (circleLinear n).mkContinuous 2 (fun u => circleMap_norm_le u)

theorem circleL_apply {n : ℕ} (u : periodicSubmodule n) : circleL n u = circleMap u := rfl

theorem circleL_norm_le (n : ℕ) : ‖circleL n‖ ≤ 2 := by
  change sInf {c : ℝ | 0 ≤ c ∧ ∀ u : periodicSubmodule n, ‖circleMap u‖ ≤ c * ‖u‖} ≤ 2
  apply csInf_le
  · exact ⟨0, fun _ hc => hc.1⟩
  · exact ⟨by norm_num, circleMap_norm_le⟩

theorem circleMap_injective (n : ℕ) : Function.Injective (circleMap (n := n)) := by
  intro u v h
  apply Subtype.ext
  apply h1_eq_of_representative_eq
  intro t
  rw [← circleMap_coe u t.property, ← circleMap_coe v t.property, h]

theorem circleMap_continuous (n : ℕ) : Continuous (circleMap (n := n)) :=
  (circleL n).continuous

theorem circleEvaluation_continuous (n : ℕ) :
    Continuous (fun p : periodicSubmodule n × Circle => circleMap p.1 p.2) := by
  exact continuous_eval.comp ((circleMap_continuous n).comp continuous_fst |>.prodMk continuous_snd)

def realMap {n : ℕ} (u : periodicSubmodule n) : C(ℝ, Ambient n) :=
  (circleMap u).comp ⟨fun t => (t : Circle), AddCircle.continuous_mk' 1⟩

theorem realMap_apply {n : ℕ} (u : periodicSubmodule n) (t : ℝ) :
    realMap u t = circleMap u (t : Circle) := rfl

theorem realMap_eqOn {n : ℕ} (u : periodicSubmodule n) :
    EqOn (realMap u) (continuousRepresentative (u : Space n)) (Icc 0 1) :=
  fun _ ht => circleMap_coe u ht

theorem realMap_periodic {n : ℕ} (u : periodicSubmodule n) : Function.Periodic (realMap u) 1 := by
  intro t
  change circleMap u ((t + 1 : ℝ) : Circle) = circleMap u (t : Circle)
  rw [AddCircle.coe_add_period]

theorem realEvaluation_continuous (n : ℕ) :
    Continuous (fun p : periodicSubmodule n × ℝ => realMap p.1 p.2) :=
  (circleEvaluation_continuous n).comp
    (continuous_fst.prodMk ((AddCircle.continuous_mk' 1).comp continuous_snd))

theorem sphereLoop_periodicData_continuous (n : ℕ) :
    Continuous (fun u : SphereLoop n => u.data) := by
  apply Continuous.subtype_mk
  exact (sphereLoop_data_isometry n).continuous

theorem circleMap_sphere_norm {n : ℕ} (u : SphereLoop n) (x : Circle) :
    ‖circleMap u.data x‖ = 1 := by
  rw [circleMap_apply]
  exact u.sphere_constraint (circlePoint x)

def sphereCircleMap {n : ℕ} (u : SphereLoop n) : C(Circle, Sphere n) :=
  ⟨fun x => ⟨circleMap u.data x, by
      rw [mem_sphere_zero_iff_norm]
      exact circleMap_sphere_norm u x⟩,
    (circleMap u.data).continuous.subtype_mk _⟩

theorem sphereCircleMap_val {n : ℕ} (u : SphereLoop n) (x : Circle) :
    (sphereCircleMap u x : Ambient n) = circleMap u.data x := rfl

theorem sphereCircleMap_point {n : ℕ} (u : SphereLoop n) (x : Circle) :
    sphereCircleMap u x = sphereRepresentative u (circlePoint x) := by
  apply Subtype.ext
  exact circleMap_apply u.data x

theorem sphereCircleMap_coe {n : ℕ} (u : SphereLoop n) (t : ClosedInterval) :
    sphereCircleMap u (t : ℝ) = sphereRepresentative u t := by
  apply Subtype.ext
  exact circleMap_coe u.data t.property

theorem sphereCircleMap_injective (n : ℕ) : Function.Injective (sphereCircleMap (n := n)) := by
  intro u v h
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [← sphereCircleMap_coe u t, ← sphereCircleMap_coe v t, h]

theorem sphereCircleEvaluation_continuous (n : ℕ) :
    Continuous (fun p : SphereLoop n × Circle => sphereCircleMap p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : SphereLoop n × Circle => circleMap p.1.data p.2)
  have hc : Continuous (fun u : SphereLoop n => circleMap u.data) :=
    (circleMap_continuous n).comp (sphereLoop_periodicData_continuous n)
  exact continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd)

theorem sphereCircleMap_continuous (n : ℕ) : Continuous (sphereCircleMap (n := n)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (sphereCircleEvaluation_continuous n)

theorem sphereCircleMap_image {n : ℕ} (u : SphereLoop n) :
    Set.range (sphereCircleMap u) = sphereImage u := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨circlePoint x, (sphereCircleMap_point u x).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(t : ℝ), sphereCircleMap_coe u t⟩

def shiftedSphereMap {n : ℕ} (u : SphereLoop n) (a : Circle) : C(Circle, Sphere n) :=
  (sphereCircleMap u).comp ⟨fun x => a + x, continuous_const.add continuous_id⟩

theorem shiftedSphereMap_apply {n : ℕ} (u : SphereLoop n) (a x : Circle) :
    shiftedSphereMap u a x = sphereCircleMap u (a + x) := rfl

theorem shiftedSphereMap_zero {n : ℕ} (u : SphereLoop n) :
    shiftedSphereMap u 0 = sphereCircleMap u := by
  apply ContinuousMap.ext
  intro x
  change sphereCircleMap u (0 + x) = sphereCircleMap u x
  rw [zero_add]

theorem shiftedSphereMap_add {n : ℕ} (u : SphereLoop n) (a b x : Circle) :
    shiftedSphereMap u (a + b) x = shiftedSphereMap u a (b + x) := by
  change sphereCircleMap u ((a + b) + x) = sphereCircleMap u (a + (b + x))
  rw [add_assoc]

theorem shiftedSphereMap_image {n : ℕ} (u : SphereLoop n) (a : Circle) :
    Set.range (shiftedSphereMap u a) = sphereImage u := by
  rw [← sphereCircleMap_image]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨a + x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨-a + x, ?_⟩
    change sphereCircleMap u (a + (-a + x)) = sphereCircleMap u x
    rw [← add_assoc, add_neg_cancel, zero_add]

theorem shiftedSphereEvaluation_continuous (n : ℕ) :
    Continuous (fun p : (SphereLoop n × Circle) × Circle => shiftedSphereMap p.1.1 p.1.2 p.2) :=
  (sphereCircleEvaluation_continuous n).comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.add continuous_snd))

theorem shiftedSphereMap_continuous (n : ℕ) :
    Continuous (fun p : SphereLoop n × Circle => shiftedSphereMap p.1 p.2) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (shiftedSphereEvaluation_continuous n)

end

end Finsler.SobolevCircleRepresentative
