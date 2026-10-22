module

public import Finsler.Analysis.H1PaddingTime
public import Finsler.Analysis.IntervalH1WeakLimit
public import Finsler.Geometry.RoundMetric

/-! Strong-H1 continuity of padding, including zero, by the existing Radon-Riesz theorem.
The actual round metric computes the velocity norm, avoiding a new L2 dilation theory. -/

@[expose] public section

namespace Finsler.H1PaddingContinuity

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1ConstantPadding Finsler.H1PaddingTime Finsler.SobolevEnergy
open Finsler.SobolevEnergyDifferential Finsler.AmbientLagrangian Finsler.SphereRetraction
open Finsler.BorelLoop MeasureTheory Set Filter
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

theorem round_energy_norm {n : ℕ} (u : SphereLoop n) :
    energy (roundMetric n) u = ‖velocity (u.data : Space n)‖ ^ 2 := by
  have he : (fun t => lagrangian (roundMetric n) (weakJet u t)) =ᵐ[intervalMeasure]
      fun t => ‖velocity (u.data : Space n) t‖ ^ 2 := by
    filter_upwards [weakJet_has_tangent_ae u] with t ht
    obtain ⟨p, hp⟩ := ht
    have hv : ambientVector n p = velocity (u.data : Space n) t := congrArg Prod.snd hp
    rw [← hp, lagrangian_ambientPair]
    change ‖ambientVector n p‖ ^ 2 = _
    rw [hv]
  rw [SobolevEnergy.energy, integral_congr_ae he, lp_two_norm_eq_sqrt_integral_norm_sq,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

theorem velocity_padded_norm_sq {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u : SphereLoop n) :
    ‖velocity ((padded a ha0 ha1 u).data : Space n)‖ ^ 2 =
      ‖velocity (u.data : Space n)‖ ^ 2 / (1 - a) := by
  rw [← round_energy_norm, energy_padded, round_energy_norm]

theorem velocity_padded_norm {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u : SphereLoop n) :
    ‖velocity ((padded a ha0 ha1 u).data : Space n)‖ =
      Real.sqrt (‖velocity (u.data : Space n)‖ ^ 2 / (1 - a)) := by
  rw [← velocity_padded_norm_sq a ha0 ha1 u, Real.sqrt_sq (norm_nonneg _)]

abbrev Parameters := Ico (0 : ℝ) 1

theorem continuous_time (t : ClosedInterval) :
    Continuous (fun a : Parameters => time a t) := by
  unfold time
  exact continuous_const.max ((continuous_const.sub continuous_subtype_val).div
    (continuous_const.sub continuous_subtype_val) (fun a => (sub_pos.mpr a.property.2).ne'))

theorem continuous_representative {n : ℕ} (t : ClosedInterval) :
    Continuous (fun z : Parameters × SphereLoop n =>
      continuousRepresentative ((padded z.1 z.1.property.1 z.1.property.2 z.2).data : Space n) t) := by
  have hf : Continuous (fun z : Parameters × SphereLoop n =>
      representativeL n (z.2.data : Space n)) :=
    (representativeL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp continuous_snd)
  have ht : Continuous (fun z : Parameters × SphereLoop n =>
      (⟨time z.1 t, time_mem z.1.property.1 z.1.property.2 t.property⟩ : ClosedInterval)) :=
    ((continuous_time t).comp continuous_fst).subtype_mk _
  have he := continuous_eval.comp (hf.prodMk ht)
  exact he.congr (fun z => (representative_padded z.1 z.1.property.1 z.1.property.2 z.2 t).symm)

theorem continuous_velocity_norm {n : ℕ} :
    Continuous (fun z : Parameters × SphereLoop n =>
      ‖velocity ((padded z.1 z.1.property.1 z.1.property.2 z.2).data : Space n)‖) := by
  have hu : Continuous (fun z : Parameters × SphereLoop n => velocity (z.2.data : Space n)) :=
    (velocityL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp continuous_snd)
  have ha : Continuous (fun z : Parameters × SphereLoop n => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have he := Real.continuous_sqrt.comp ((hu.norm.pow 2).div (continuous_const.sub ha)
    (fun z => (sub_pos.mpr z.1.property.2).ne'))
  exact he.congr (fun z => (velocity_padded_norm z.1 z.1.property.1 z.1.property.2 z.2).symm)

theorem continuous_padded {n : ℕ} :
    Continuous (fun z : Parameters × SphereLoop n =>
      padded z.1 z.1.property.1 z.1.property.2 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply sphereLoop_tendsto_iff.mpr
  apply SobolevWeakLimit.tendsto_of_representative_norm
  · intro t ht
    exact (continuous_representative (n := n) ⟨t, ht⟩).continuousAt
  · exact (continuous_velocity_norm (n := n)).continuousAt

end
end Finsler.H1PaddingContinuity

