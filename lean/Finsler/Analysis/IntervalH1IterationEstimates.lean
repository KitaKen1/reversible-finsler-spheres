module

public import Finsler.Analysis.IntervalH1IterationEnergy

/-! Linear and metric estimates for genuine positive H¹ iteration.
The original weak graph norm gives both a distance lower bound and a k-Lipschitz
upper bound. These will certify continuity of the half-period inverse. -/

@[expose] public section

namespace Finsler.SobolevIteration

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.CircleLpTransfer
open scoped Topology NNReal

noncomputable section

theorem iterateData_add {n : ℕ} (u v : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateData (u + v) k hk = iterateData u k hk + iterateData v k hk := by
  apply h1_value_injective
  calc
    value (iterateData (u + v) k hk) = iterateLpL (Ambient n) k hk
        (value ((u + v : periodicSubmodule n) : Space n)) := value_iterateData (u + v) k hk
    _ = iterateLpL (Ambient n) k hk (value (u : Space n) + value (v : Space n)) :=
      congrArg (iterateLpL (Ambient n) k hk) ((valueL n).map_add (u : Space n) (v : Space n))
    _ = iterateLpL (Ambient n) k hk (value (u : Space n)) +
        iterateLpL (Ambient n) k hk (value (v : Space n)) :=
      (iterateLpL (Ambient n) k hk).map_add (value (u : Space n)) (value (v : Space n))
    _ = value (iterateData u k hk) + value (iterateData v k hk) :=
      congrArg₂ (fun f g : ValueLp n => f + g) (value_iterateData u k hk).symm
        (value_iterateData v k hk).symm
    _ = value (iterateData u k hk + iterateData v k hk) :=
      ((valueL n).map_add (iterateData u k hk) (iterateData v k hk)).symm

theorem iterateData_smul {n : ℕ} (c : ℝ) (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateData (c • u) k hk = c • iterateData u k hk := by
  apply h1_value_injective
  calc
    value (iterateData (c • u) k hk) = iterateLpL (Ambient n) k hk
        (value ((c • u : periodicSubmodule n) : Space n)) := value_iterateData (c • u) k hk
    _ = iterateLpL (Ambient n) k hk (c • value (u : Space n)) :=
      congrArg (iterateLpL (Ambient n) k hk) ((valueL n).map_smul c (u : Space n))
    _ = c • iterateLpL (Ambient n) k hk (value (u : Space n)) :=
      (iterateLpL (Ambient n) k hk).map_smul c (value (u : Space n))
    _ = c • value (iterateData u k hk) :=
      congrArg (fun f : ValueLp n => c • f) (value_iterateData u k hk).symm
    _ = value (c • iterateData u k hk) := ((valueL n).map_smul c (iterateData u k hk)).symm

def iterationLinear (n k : ℕ) (hk : k ≠ 0) : periodicSubmodule n →ₗ[ℝ] Space n where
  toFun u := iterateData u k hk
  map_add' u v := iterateData_add u v k hk
  map_smul' c u := iterateData_smul c u k hk

theorem iterateData_sub {n : ℕ} (u v : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateData (u - v) k hk = iterateData u k hk - iterateData v k hk :=
  (iterationLinear n k hk).map_sub u v

theorem norm_le_iterateData {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    ‖(u : Space n)‖ ≤ ‖iterateData u k hk‖ := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hi := iterateData_norm_sq u k hk
  have hu := norm_sq_eq (u : Space n)
  have hp : 0 ≤ ((k : ℝ) ^ 2 - 1) * ‖velocity (u : Space n)‖ ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  nlinarith [norm_nonneg (u : Space n), norm_nonneg (iterateData u k hk)]

theorem iterateData_norm_le {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    ‖iterateData u k hk‖ ≤ (k : ℝ) * ‖(u : Space n)‖ := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hi := iterateData_norm_sq u k hk
  have hu := norm_sq_eq (u : Space n)
  have hp : 0 ≤ ((k : ℝ) ^ 2 - 1) * ‖value (u : Space n)‖ ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have hsq : ‖iterateData u k hk‖ ^ 2 ≤ ((k : ℝ) * ‖(u : Space n)‖) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (norm_nonneg _))).mp hsq

theorem dist_le_iterateData {n : ℕ} (u v : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    dist (u : Space n) (v : Space n) ≤ dist (iterateData u k hk) (iterateData v k hk) := by
  have h := norm_le_iterateData (u - v) k hk
  rw [iterateData_sub] at h
  simpa only [dist_eq_norm, Submodule.coe_sub] using h

theorem iterateData_dist_le {n : ℕ} (u v : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    dist (iterateData u k hk) (iterateData v k hk) ≤ (k : ℝ) * dist (u : Space n) (v : Space n) := by
  have h := iterateData_norm_le (u - v) k hk
  rw [iterateData_sub] at h
  simpa only [dist_eq_norm, Submodule.coe_sub] using h

theorem dist_le_iterateSphere {n : ℕ} (u v : SphereLoop n) (k : ℕ) (hk : k ≠ 0) :
    dist u v ≤ dist (iterateSphere u k hk) (iterateSphere v k hk) := by
  change dist (u.data : Space n) (v.data : Space n) ≤
    dist (iterateData u.data k hk) (iterateData v.data k hk)
  exact dist_le_iterateData u.data v.data k hk

theorem iterateSphere_lipschitz (n k : ℕ) (hk : k ≠ 0) :
    LipschitzWith (k : ℝ≥0) (fun u : SphereLoop n => iterateSphere u k hk) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (iterateData u.data k hk) (iterateData v.data k hk) ≤
    (k : ℝ) * dist (u.data : Space n) (v.data : Space n)
  exact iterateData_dist_le u.data v.data k hk

end

end Finsler.SobolevIteration
