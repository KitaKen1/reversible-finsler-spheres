module

public import Finsler.Analysis.IntervalH1RotationIsometry
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Actual L² pullback by a positive-degree covering of the standard circle.
The interval operator uses the already proved inverse measure-preserving maps.
It is an isometry, including on the genuine periodized weak velocity. -/

@[expose] public section

namespace Finsler.SobolevIteration

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CircleLpTransfer
open Finsler.SobolevCircleRepresentative Finsler.SobolevPeriodicVelocity
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def degreeCover (k : ℕ) : C(Phase, Phase) :=
  ⟨fun x => k • x, continuous_id.nsmul k⟩

theorem degreeCover_apply (k : ℕ) (x : Phase) : degreeCover k x = k • x := rfl

theorem degreeCover_coe (k : ℕ) (t : ℝ) :
    degreeCover k (t : Phase) = ((k : ℝ) * t : ℝ) := by
  change k • (t : Phase) = (((k : ℝ) * t : ℝ) : Phase)
  rw [← nsmul_eq_mul, AddCircle.coe_nsmul]

theorem degreeCover_measurePreserving (k : ℕ) (hk : k ≠ 0) :
    MeasurePreserving (degreeCover k) (volume : Measure Phase) volume := by
  have h := Measure.measurePreserving_zsmul (volume : Measure Phase) (Int.natCast_ne_zero.mpr hk)
  simpa only [natCast_zsmul, degreeCover] using! h

def coverLpL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (hk : k ≠ 0) : CircleLp E →L[ℝ] CircleLp E :=
  (Lp.compMeasurePreservingₗᵢ ℝ (degreeCover k)
    (degreeCover_measurePreserving k hk)).toContinuousLinearMap

theorem coverLpL_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleLp E) (k : ℕ) (hk : k ≠ 0) :
    coverLpL E k hk f =ᵐ[volume] fun x => f (degreeCover k x) :=
  Lp.coeFn_compMeasurePreserving f (degreeCover_measurePreserving k hk)

theorem coverLpL_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleLp E) (k : ℕ) (hk : k ≠ 0) : ‖coverLpL E k hk f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (degreeCover_measurePreserving k hk)

def iterateLpL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (hk : k ≠ 0) : Lp E 2 intervalMeasure →L[ℝ] Lp E 2 intervalMeasure :=
  (toIntervalL E).comp ((coverLpL E k hk).comp (toCircleL E))

theorem iterateLpL_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 intervalMeasure) (k : ℕ) (hk : k ≠ 0) :
    iterateLpL E k hk f =ᵐ[intervalMeasure]
      fun t => f (sectionPoint (degreeCover k (t : Phase))) := by
  filter_upwards [toIntervalL_ae (coverLpL E k hk (toCircleL E f)),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (coverLpL_ae (toCircleL E f) k hk),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      ((degreeCover_measurePreserving k hk).quasiMeasurePreserving.ae_eq_comp
        (toCircleL_ae f))] with t h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃)

theorem iterateLpL_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 intervalMeasure) (k : ℕ) (hk : k ≠ 0) :
    ‖iterateLpL E k hk f‖ = ‖f‖ := by
  change ‖toIntervalL E (coverLpL E k hk (toCircleL E f))‖ = _
  rw [toIntervalL_norm, coverLpL_norm, toCircleL_norm]

theorem iterateLpL_value_ae {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateLpL (Ambient n) k hk (value (u : Space n)) =ᵐ[intervalMeasure]
      fun t => realMap u ((k : ℝ) * t) := by
  filter_upwards [toIntervalL_ae (coverLpL (Ambient n) k hk
      (toCircleL (Ambient n) (value (u : Space n)))),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (coverLpL_ae (toCircleL (Ambient n) (value (u : Space n))) k hk),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      ((degreeCover_measurePreserving k hk).quasiMeasurePreserving.ae_eq_comp
        (Finsler.SobolevRotation.value_toCircle_ae u))] with t h₁ h₂ h₃
  exact h₁.trans (h₂.trans (h₃.trans (by
    change circleMap u (degreeCover k (t : Phase)) = realMap u ((k : ℝ) * t)
    rw [degreeCover_coe, realMap_apply])))

theorem iterateLpL_velocity_ae {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateLpL (Ambient n) k hk (velocity (u : Space n)) =ᵐ[intervalMeasure]
      fun t => periodicVelocity u ((k : ℝ) * t) := by
  filter_upwards [iterateLpL_ae (velocity (u : Space n)) k hk] with t ht
  exact ht.trans (by rw [degreeCover_coe]; rfl)

theorem rescaledVelocity_memLp {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    MemLp (fun t => (k : ℝ) • periodicVelocity u ((k : ℝ) * t)) 2 intervalMeasure :=
  ((Lp.memLp (iterateLpL (Ambient n) k hk (velocity (u : Space n)))).ae_eq
    (iterateLpL_velocity_ae u k hk)).const_smul (k : ℝ)

end

end Finsler.SobolevIteration
