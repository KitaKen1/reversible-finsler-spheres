module

public import Finsler.Analysis.IntervalH1Constant
public import Finsler.Analysis.IntervalPrimitive
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Continuous representatives of the actual vector-valued interval H¹ graph.
The primitive is constructed from its L² weak velocity. No continuity or
classical differentiability of the original L² representative is assumed.
Periodic traces, the sphere constraint and energy differentiability are separate. -/

@[expose] public section

namespace Finsler.IntervalSobolev

open Finsler.SphereGeometry MeasureTheory Set Filter
open scoped Topology

noncomputable section

theorem velocity_integrable {n : ℕ} (u : Space n) :
    Integrable (velocity u) intervalMeasure := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
    infer_instance
  exact (Lp.memLp (velocity u)).integrable (by norm_num)

theorem velocity_intervalIntegrable {n : ℕ} (u : Space n) :
    IntervalIntegrable (velocity u) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact velocity_integrable u

theorem value_hasWeakLineVelocity {n : ℕ} (u : Space n) :
    TauCeti.HasWeakLineDerivOn volume ⟨Ioo 0 1, isOpen_Ioo⟩ (value u) (velocity u) 1 := by
  have h := (TauCeti.hasWeakFDerivOn_iff.mp (value_hasWeakFDeriv u)) (1 : ℝ)
  exact h.congr_ae_deriv (velocity_apply_ae u).symm

theorem exists_ae_eq_const_add_primitive {n : ℕ} (u : Space n) :
    ∃ c : Ambient n, value u =ᵐ[intervalMeasure]
      fun t => c + Finsler.IntervalPrimitive.primitive (velocity u) t := by
  obtain ⟨c, hc⟩ := Finsler.IntervalWeakConstant.exists_ae_const_of_equal_weak_derivatives
    (value_hasWeakLineVelocity u)
    (Finsler.IntervalPrimitive.primitive_hasWeakLineDeriv (velocity_intervalIntegrable u))
  refine ⟨c, ?_⟩
  filter_upwards [hc] with t ht
  exact sub_eq_iff_eq_add.mp ht

theorem exists_continuous_representative {n : ℕ} (u : Space n) :
    ∃ q : ℝ → Ambient n, ContinuousOn q (Icc 0 1) ∧
      value u =ᵐ[intervalMeasure] q ∧
      ∃ c : Ambient n, ∀ t, q t = c + Finsler.IntervalPrimitive.primitive (velocity u) t := by
  obtain ⟨c, hc⟩ := exists_ae_eq_const_add_primitive u
  refine ⟨fun t => c + Finsler.IntervalPrimitive.primitive (velocity u) t, ?_, hc, c, ?_⟩
  · exact continuousOn_const.add
      (Finsler.IntervalPrimitive.primitive_continuousOn (velocity_intervalIntegrable u))
  · intro t
    rfl

theorem continuous_representative_unique {n : ℕ} {u : Space n} {q r : ℝ → Ambient n}
    (hq : ContinuousOn q (Icc 0 1)) (hr : ContinuousOn r (Icc 0 1))
    (huq : value u =ᵐ[intervalMeasure] q) (hur : value u =ᵐ[intervalMeasure] r) :
    EqOn q r (Icc 0 1) := by
  have hqr := huq.symm.trans hur
  change q =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] r at hqr
  rw [restrict_Ioo_eq_restrict_Icc] at hqr
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hqr hq hr

def continuousRepresentative {n : ℕ} (u : Space n) : ℝ → Ambient n :=
  (exists_continuous_representative u).choose

theorem continuousRepresentative_continuousOn {n : ℕ} (u : Space n) :
    ContinuousOn (continuousRepresentative u) (Icc 0 1) :=
  (exists_continuous_representative u).choose_spec.1

theorem value_ae_continuousRepresentative {n : ℕ} (u : Space n) :
    value u =ᵐ[intervalMeasure] continuousRepresentative u :=
  (exists_continuous_representative u).choose_spec.2.1

theorem continuousRepresentative_sub {n : ℕ} (u : Space n) {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    continuousRepresentative u t - continuousRepresentative u s =
      ∫ x in s..t, velocity u x := by
  obtain ⟨c, hc⟩ := (exists_continuous_representative u).choose_spec.2.2
  have h0 (z : ℝ) (hz : z ∈ Icc 0 1) : IntervalIntegrable (velocity u) volume 0 z := by
    refine ⟨(velocity_intervalIntegrable u).1.mono_set (Ioc_subset_Ioc le_rfl hz.2), ?_⟩
    simp only [Ioc_eq_empty (not_lt.mpr hz.1), integrableOn_empty]
  change (exists_continuous_representative u).choose t -
    (exists_continuous_representative u).choose s = _
  rw [hc t, hc s, add_sub_add_left_eq_sub]
  change (∫ x in (0 : ℝ)..t, velocity u x) - (∫ x in (0 : ℝ)..s, velocity u x) = _
  exact intervalIntegral.integral_interval_sub_left (h0 t ht) (h0 s hs)

def traceZero {n : ℕ} (u : Space n) : Ambient n := continuousRepresentative u 0

def traceOne {n : ℕ} (u : Space n) : Ambient n := continuousRepresentative u 1

theorem trace_difference {n : ℕ} (u : Space n) :
    traceOne u - traceZero u = ∫ x in (0 : ℝ)..1, velocity u x := by
  exact continuousRepresentative_sub u (by norm_num) (by norm_num)

theorem trace_eq_iff_velocity_integral_eq_zero {n : ℕ} (u : Space n) :
    traceOne u = traceZero u ↔ (∫ x in (0 : ℝ)..1, velocity u x) = 0 := by
  rw [← trace_difference, sub_eq_zero]

end

end Finsler.IntervalSobolev
