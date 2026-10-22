module

public import Finsler.Analysis.IntervalH1RotationContinuity

/-! Genuine strong-H¹ isometries and continuous circle actions on actual energy
cuts. These use the original weak graph norm and the original sqrt-energy cuts.
No Borel cohomology or Gysin sequence is asserted here. -/

@[expose] public section

namespace Finsler.SobolevRotation

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevShift Finsler.SobolevCircleAction
open Finsler.CircleLpTransfer Finsler.SobolevShiftEnergy Finsler.SobolevReflectionAction
open Finsler.Geometry
open scoped Topology

noncomputable section

theorem phaseShiftData_norm {n : ℕ} (u : periodicSubmodule n) (a : Phase) :
    ‖phaseShiftData u a‖ = ‖u‖ := by
  have hv : ‖value (phaseShiftData u a)‖ = ‖value (u : Space n)‖ :=
    (congrArg (fun f : ValueLp n => ‖f‖) (value_phaseShiftData u a)).trans
      (rotateLpL_norm (value (u : Space n)) a)
  have hw : ‖velocity (phaseShiftData u a)‖ = ‖velocity (u : Space n)‖ :=
    (congrArg (fun f : ValueLp n => ‖f‖) (velocity_phaseShiftData u a)).trans
      (rotateLpL_norm (velocity (u : Space n)) a)
  have hs : ‖phaseShiftData u a‖ ^ 2 = ‖(u : Space n)‖ ^ 2 :=
    (norm_sq_eq (phaseShiftData u a)).trans
      ((congrArg₂ (fun x y : ℝ => x ^ 2 + y ^ 2) hv hw).trans
        (norm_sq_eq (u : Space n)).symm)
  change ‖phaseShiftData u a‖ = ‖(u : Space n)‖
  nlinarith [norm_nonneg (phaseShiftData u a), norm_nonneg (u : Space n)]

theorem phaseShiftData_add {n : ℕ} (u v : periodicSubmodule n) (a : Phase) :
    phaseShiftData (u + v) a = phaseShiftData u a + phaseShiftData v a := by
  apply h1_value_injective
  calc
    value (phaseShiftData (u + v) a) = rotateLpL (Ambient n) a
        (value ((u + v : periodicSubmodule n) : Space n)) := value_phaseShiftData (u + v) a
    _ = rotateLpL (Ambient n) a (value (u : Space n) + value (v : Space n)) :=
      congrArg (rotateLpL (Ambient n) a) ((valueL n).map_add (u : Space n) (v : Space n))
    _ = rotateLpL (Ambient n) a (value (u : Space n)) +
        rotateLpL (Ambient n) a (value (v : Space n)) :=
      (rotateLpL (Ambient n) a).map_add (value (u : Space n)) (value (v : Space n))
    _ = value (phaseShiftData u a) + value (phaseShiftData v a) :=
      congrArg₂ (fun f g : ValueLp n => f + g) (value_phaseShiftData u a).symm
        (value_phaseShiftData v a).symm
    _ = value (phaseShiftData u a + phaseShiftData v a) :=
      ((valueL n).map_add (phaseShiftData u a) (phaseShiftData v a)).symm

theorem phaseShiftData_smul {n : ℕ} (c : ℝ) (u : periodicSubmodule n) (a : Phase) :
    phaseShiftData (c • u) a = c • phaseShiftData u a := by
  apply h1_value_injective
  calc
    value (phaseShiftData (c • u) a) = rotateLpL (Ambient n) a
        (value ((c • u : periodicSubmodule n) : Space n)) := value_phaseShiftData (c • u) a
    _ = rotateLpL (Ambient n) a (c • value (u : Space n)) :=
      congrArg (rotateLpL (Ambient n) a) ((valueL n).map_smul c (u : Space n))
    _ = c • rotateLpL (Ambient n) a (value (u : Space n)) :=
      (rotateLpL (Ambient n) a).map_smul c (value (u : Space n))
    _ = c • value (phaseShiftData u a) :=
      congrArg (fun f : ValueLp n => c • f) (value_phaseShiftData u a).symm
    _ = value (c • phaseShiftData u a) := ((valueL n).map_smul c (phaseShiftData u a)).symm

def rotationLI (n : ℕ) (a : Phase) : periodicSubmodule n →ₗᵢ[ℝ] Space n where
  toFun u := phaseShiftData u a
  map_add' u v := phaseShiftData_add u v a
  map_smul' c u := phaseShiftData_smul c u a
  norm_map' u := phaseShiftData_norm u a

theorem rotationLI_apply {n : ℕ} (a : Phase) (u : periodicSubmodule n) :
    rotationLI n a u = phaseShiftData u a := rfl

theorem phaseShiftData_isometry (n : ℕ) (a : Phase) :
    Isometry (fun u : periodicSubmodule n => phaseShiftData u a) := (rotationLI n a).isometry

theorem rotateSphere_isometry (n : ℕ) (a : Phase) :
    Isometry (fun u : SphereLoop n => rotateSphere u a) := by
  intro u v
  change edist (phaseShiftData u.data a) (phaseShiftData v.data a) =
    edist (u.data : Space n) (v.data : Space n)
  exact (phaseShiftData_isometry n a) u.data v.data

theorem vadd_isometry (n : ℕ) (a : Phase) :
    Isometry (fun u : SphereLoop n => a +ᵥ u) := rotateSphere_isometry n a

theorem vadd_dist {n : ℕ} (a : Phase) (u v : SphereLoop n) :
    dist (a +ᵥ u) (a +ᵥ v) = dist u v := (vadd_isometry n a).dist_eq u v

theorem shiftSphere_joint_continuous (n : ℕ) :
    Continuous (fun p : SphereLoop n × ℝ => shiftSphere p.1 p.2) := by
  have hc : Continuous (fun t : ℝ => (t : Phase)) := AddCircle.continuous_mk' (1 : ℝ)
  have h : Continuous (fun p : SphereLoop n × ℝ => (p.2 : Phase) +ᵥ p.1) :=
    (hc.comp continuous_snd).vadd continuous_fst
  simpa only [vadd_eq_rotateSphere, rotateSphere_coe] using h

instance {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    ContinuousVAdd Phase (energyCut F b) where
  continuous_vadd := by
    apply Continuous.subtype_mk
    exact continuous_fst.vadd (continuous_subtype_val.comp continuous_snd)

theorem energyCut_action_continuous {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    Continuous (fun p : Phase × energyCut F b => p.1 +ᵥ p.2) := continuous_vadd

theorem energyCut_vadd_isometry {n : ℕ} (F : ReversibleMetric n) (b : ℝ) (a : Phase) :
    Isometry (fun u : energyCut F b => a +ᵥ u) := by
  intro u v
  exact (vadd_isometry n a) (u : SphereLoop n) (v : SphereLoop n)

theorem cutInclusion_vadd {n : ℕ} (F : ReversibleMetric n) {b c : ℝ} (hbc : b ≤ c)
    (a : Phase) (u : energyCut F b) :
    cutInclusion F hbc (a +ᵥ u) = a +ᵥ cutInclusion F hbc u := Subtype.ext rfl

end

end Finsler.SobolevRotation
