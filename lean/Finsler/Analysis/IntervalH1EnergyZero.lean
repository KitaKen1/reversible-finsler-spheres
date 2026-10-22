module

public import Finsler.Analysis.IntervalH1Energy

/-! Zero actual sphere H¹ energy is exactly the actual constant-loop locus.
Weak derivative uniqueness first shows that actual H¹ graph data are determined
by their values. The energy comparison and Hölder estimate then exclude any
additional zero-energy loop; no regularity or nondegeneracy is assumed. -/

@[expose] public section

namespace Finsler.SobolevEnergy

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.Geometry
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

theorem h1_value_injective {n : ℕ} : Function.Injective (value (n := n)) := by
  intro u v h
  apply TauCeti.WeakDerivStep.ext
  change TauCeti.WeakDerivStep.prevL (base n) u =
    TauCeti.WeakDerivStep.prevL (base n) v at h
  rw [TauCeti.WeakDerivStep.prevL_apply, TauCeti.WeakDerivStep.prevL_apply] at h
  exact h

theorem h1_eq_of_representative_eq {n : ℕ} {u v : Space n}
    (h : ∀ t : ClosedInterval, continuousRepresentative u t = continuousRepresentative v t) :
    u = v := by
  apply h1_value_injective
  apply Lp.ext
  filter_upwards [value_ae_continuousRepresentative u, value_ae_continuousRepresentative v,
    ae_restrict_mem measurableSet_Ioo] with t hu hv ht
  exact hu.trans ((h ⟨t, Ioo_subset_Icc_self ht⟩).trans hv.symm)

theorem sphereLoop_eq_of_representative_eq {n : ℕ} {u v : SphereLoop n}
    (h : ∀ t : ClosedInterval, sphereRepresentative u t = sphereRepresentative v t) : u = v := by
  apply sphereLoop_data_injective
  apply h1_eq_of_representative_eq
  intro t
  exact congrArg (fun x : Sphere n => (x : Ambient n)) (h t)

theorem velocity_eq_zero_of_energy_eq_zero {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n)
    (hE : energy F u = 0) : velocity (u.data : Space n) = 0 := by
  obtain ⟨c, C, hc, _hC, hb⟩ := exists_energy_norm_bounds F
  have hl := (hb u).1
  rw [hE] at hl
  have hs : ‖velocity (u.data : Space n)‖ ^ 2 ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge hl) (mul_pos hc (lt_of_not_ge hn))
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (velocity (u.data : Space n))]

theorem sphereLoop_eq_constant_of_velocity_eq_zero {n : ℕ} (u : SphereLoop n)
    (hv : velocity (u.data : Space n) = 0) :
    u = constantSphereLoop (sphereRepresentative u ⟨0, by norm_num⟩) := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_constantSphereLoop]
  apply Subtype.ext
  change continuousRepresentative (u.data : Space n) t =
    continuousRepresentative (u.data : Space n) 0
  have hh := continuousRepresentative_holder_half (u.data : Space n)
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) t.property
  rw [hv, norm_zero, mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

theorem energy_constantSphereLoop {n : ℕ} (F : ReversibleMetric n) (x : Sphere n) :
    energy F (constantSphereLoop x) = 0 := by
  obtain ⟨c, C, _hc, _hC, hb⟩ := exists_energy_norm_bounds F
  have hv : velocity ((constantSphereLoop x).data : Space n) = 0 := by
    change velocity (constantData (x : Ambient n)) = 0
    exact velocity_constantData (x : Ambient n)
  have hu := (hb (constantSphereLoop x)).2
  rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hu
  exact le_antisymm hu (energy_nonneg F _)

theorem energy_eq_zero_iff_constant {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    energy F u = 0 ↔ ∃ x : Sphere n, u = constantSphereLoop x := by
  constructor
  · intro hE
    exact ⟨sphereRepresentative u ⟨0, by norm_num⟩,
      sphereLoop_eq_constant_of_velocity_eq_zero u (velocity_eq_zero_of_energy_eq_zero F u hE)⟩
  · rintro ⟨x, rfl⟩
    exact energy_constantSphereLoop F x

theorem energy_pos_iff_nonconstant {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    0 < energy F u ↔ ¬ ∃ x : Sphere n, u = constantSphereLoop x := by
  constructor
  · intro hp hx
    have hz := (energy_eq_zero_iff_constant F u).mpr hx
    linarith
  · intro hn
    by_contra hp
    have hz : energy F u = 0 := le_antisymm (le_of_not_gt hp) (energy_nonneg F u)
    exact hn ((energy_eq_zero_iff_constant F u).mp hz)

end

end Finsler.SobolevEnergy
