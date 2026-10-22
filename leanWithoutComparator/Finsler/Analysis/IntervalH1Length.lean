module

public import Finsler.Geometry.PolygonBasics
public import Finsler.Analysis.IntervalH1Energy

/-! The Finsler length of actual H¹ sphere loops. The speed density √F² lies in L², its
integral is the length, and on the unit interval the length squared is at most the energy:
0 ≤ ∫(√F² − L)² = E − L² because the interval measure has total mass one. -/

@[expose] public section

namespace Finsler.SobolevLength

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevEnergy
open MeasureTheory Set

noncomputable section

variable {n : ℕ}

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

theorem intervalMeasure_univ : intervalMeasure univ = 1 := by
  change volume.restrict (Ioo (0 : ℝ) 1) univ = 1
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
  norm_num

/-- The Finsler speed density √F² of an actual H¹ sphere loop. -/
def speed (F : ReversibleMetric n) (u : SphereLoop n) (t : ℝ) : ℝ :=
  Real.sqrt (lagrangian F (weakJet u t))

theorem speed_nonneg (F : ReversibleMetric n) (u : SphereLoop n) (t : ℝ) : 0 ≤ speed F u t :=
  Real.sqrt_nonneg _

theorem speed_sq (F : ReversibleMetric n) (u : SphereLoop n) (t : ℝ) :
    speed F u t ^ 2 = lagrangian F (weakJet u t) :=
  Real.sq_sqrt (density_nonneg F u t)

theorem speed_memLp (F : ReversibleMetric n) (u : SphereLoop n) :
    MemLp (speed F u) 2 intervalMeasure := by
  have hm : AEStronglyMeasurable (speed F u) intervalMeasure :=
    (density_aestronglyMeasurable F u).aemeasurable.sqrt.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).mpr ?_
  have hfun : (fun t => speed F u t ^ 2) = fun t => lagrangian F (weakJet u t) :=
    funext (speed_sq F u)
  rw [hfun]
  exact density_integrable F u

theorem speed_integrable (F : ReversibleMetric n) (u : SphereLoop n) :
    Integrable (speed F u) intervalMeasure :=
  (speed_memLp F u).integrable (by norm_num)

/-- The Finsler length of an actual H¹ sphere loop. -/
def length (F : ReversibleMetric n) (u : SphereLoop n) : ℝ := ∫ t, speed F u t ∂intervalMeasure

theorem length_nonneg (F : ReversibleMetric n) (u : SphereLoop n) : 0 ≤ length F u :=
  integral_nonneg (speed_nonneg F u)

/-- Length squared is at most energy on the unit interval. -/
theorem length_sq_le_energy (F : ReversibleMetric n) (u : SphereLoop n) :
    length F u ^ 2 ≤ Finsler.SobolevEnergy.energy F u := by
  set L := length F u with hL
  have hi := speed_integrable F u
  have hi2 : Integrable (fun t => speed F u t ^ 2) intervalMeasure := by
    have hfun : (fun t => speed F u t ^ 2) = fun t => lagrangian F (weakJet u t) :=
      funext (speed_sq F u)
    rw [hfun]
    exact density_integrable F u
  have hnonneg : 0 ≤ ∫ t, (speed F u t - L) ^ 2 ∂intervalMeasure :=
    integral_nonneg fun t => sq_nonneg _
  have hexp : (fun t => (speed F u t - L) ^ 2) =
      fun t => speed F u t ^ 2 - (2 * L) * speed F u t + L ^ 2 := by
    funext t
    ring
  have hint : ∫ t, (speed F u t - L) ^ 2 ∂intervalMeasure =
      Finsler.SobolevEnergy.energy F u - 2 * L * L + L ^ 2 := by
    have hA : Integrable (fun t => speed F u t ^ 2 - 2 * L * speed F u t) intervalMeasure :=
      hi2.sub (hi.const_mul (2 * L))
    have hB : Integrable (fun _ : ℝ => L ^ 2) intervalMeasure := integrable_const _
    have hC : Integrable (fun t => 2 * L * speed F u t) intervalMeasure := hi.const_mul (2 * L)
    rw [hexp, integral_add hA hB, integral_sub hi2 hC, integral_const_mul, integral_const]
    have he : ∫ t, speed F u t ^ 2 ∂intervalMeasure = Finsler.SobolevEnergy.energy F u := by
      unfold Finsler.SobolevEnergy.energy
      congr 1
      funext t
      exact speed_sq F u t
    have hlen : ∫ t, speed F u t ∂intervalMeasure = L := rfl
    have hreal : intervalMeasure.real univ = 1 := by
      rw [measureReal_def, intervalMeasure_univ, ENNReal.toReal_one]
    rw [he, hlen, hreal, one_smul]
  rw [hint] at hnonneg
  nlinarith

end

end Finsler.SobolevLength
