module

public import Finsler.Analysis.IntervalH1Reparam
public import Finsler.Algebra.Normalization

/-! The Anosov normalization homotopy. For a loop of length ℓ > 0 and 0 ≤ s ≤ 1 the density
(1 − s) + s F(u, u̇)/ℓ has mass one and vanishes only at s = 1 where the speed vanishes, so it
reparametrizes the loop. The energy of the result is ∫ F²/((1 − s) + s F/ℓ), which is at most
(1 − s) E + s ℓ² by the pointwise bound of NORM-SCALAR, and equals ℓ² at s = 1. Lengths are
unchanged, the parameter 0 gives the identity, and loops of length zero are fixed. -/

@[expose] public section

namespace Finsler.NormalizationHomotopy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevEnergy Finsler.SobolevLength Finsler.SobolevReparam Finsler.MonotoneSubst
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

/-- A measurable nonnegative version of the speed. -/
def mspeed (F : ReversibleMetric n) (u : SphereLoop n) (t : ℝ) : ℝ :=
  max ((speed_memLp F u).aestronglyMeasurable.mk (speed F u) t) 0

theorem mspeed_measurable (F : ReversibleMetric n) (u : SphereLoop n) :
    Measurable (mspeed F u) :=
  (speed_memLp F u).aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const

theorem mspeed_nonneg (F : ReversibleMetric n) (u : SphereLoop n) (t : ℝ) : 0 ≤ mspeed F u t :=
  le_max_right _ _

theorem mspeed_ae (F : ReversibleMetric n) (u : SphereLoop n) :
    mspeed F u =ᵐ[intervalMeasure] speed F u := by
  filter_upwards [(speed_memLp F u).aestronglyMeasurable.ae_eq_mk] with t ht
  unfold mspeed
  rw [← ht]
  exact max_eq_left (speed_nonneg F u t)

theorem mspeed_integrable (F : ReversibleMetric n) (u : SphereLoop n) :
    Integrable (mspeed F u) intervalMeasure :=
  (speed_integrable F u).congr (mspeed_ae F u).symm

theorem integral_mspeed (F : ReversibleMetric n) (u : SphereLoop n) :
    ∫ x in (0 : ℝ)..1, mspeed F u x = length F u := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← intervalMeasure_eq]
  exact integral_congr_ae (mspeed_ae F u)

/-- The normalizing density at parameter s. -/
def normDensity (F : ReversibleMetric n) (s : ℝ) (u : SphereLoop n) (x : ℝ) : ℝ :=
  (1 - s) + s * (mspeed F u x / length F u)

/-- The kinetic integrand over the density is at most quadratic plus linear. -/
theorem inv_density_le {s L k m r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hL : 0 < L) (hk : 0 < k)
    (hr : 0 ≤ r) (hm : k * r ≤ m) :
    ((1 - s) + s * (m / L))⁻¹ * r ^ 2 ≤ 2 * r ^ 2 + 2 * L / k * r := by
  have hm0 : 0 ≤ m := (mul_nonneg hk.le hr).trans hm
  have hA : 0 ≤ s * (m / L) := mul_nonneg hs.1 (div_nonneg hm0 hL.le)
  have hR : 0 ≤ 2 * L / k * r := by positivity
  rcases le_or_gt s (1 / 2) with h | h
  · have hDpos : 0 < (1 - s) + s * (m / L) := by linarith
    have hinv : ((1 - s) + s * (m / L))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hDpos (by norm_num)]
      linarith
    calc ((1 - s) + s * (m / L))⁻¹ * r ^ 2 ≤ 2 * r ^ 2 :=
          mul_le_mul_of_nonneg_right hinv (sq_nonneg r)
      _ ≤ 2 * r ^ 2 + 2 * L / k * r := le_add_of_nonneg_right hR
  · rcases eq_or_lt_of_le hr with hr0 | hrpos
    · rw [← hr0]
      simp
    · have hD : k * r / (2 * L) ≤ (1 - s) + s * (m / L) := by
        have h1 : k * r / (2 * L) ≤ s * (m / L) := by
          rw [div_le_iff₀ (by positivity)]
          have he : s * (m / L) * (2 * L) = 2 * s * m := by
            field_simp
          rw [he]
          nlinarith
        linarith [sub_nonneg.mpr hs.2]
      have hDpos : 0 < k * r / (2 * L) := by positivity
      have hinv : ((1 - s) + s * (m / L))⁻¹ ≤ (k * r / (2 * L))⁻¹ := inv_anti₀ hDpos hD
      calc ((1 - s) + s * (m / L))⁻¹ * r ^ 2 ≤ (k * r / (2 * L))⁻¹ * r ^ 2 :=
            mul_le_mul_of_nonneg_right hinv (sq_nonneg r)
        _ = 2 * L / k * r := by
            field_simp
        _ ≤ 2 * r ^ 2 + 2 * L / k * r := le_add_of_nonneg_left (by positivity)

/-- Almost everywhere the speed dominates the Euclidean velocity norm. -/
theorem exists_speed_lower (F : ReversibleMetric n) :
    ∃ k : ℝ, 0 < k ∧ ∀ u : SphereLoop n, ∀ᵐ t ∂intervalMeasure,
      k * ‖velocity (u.data : Space n) t‖ ≤ mspeed F u t := by
  obtain ⟨c, C, hc, _hC, hb⟩ := exists_density_bounds F
  refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, fun u => ?_⟩
  filter_upwards [hb u, mspeed_ae F u] with t ht hm
  rw [hm]
  unfold speed
  calc Real.sqrt c * ‖velocity (u.data : Space n) t‖ =
        Real.sqrt (c * ‖velocity (u.data : Space n) t‖ ^ 2) := by
        rw [Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (lagrangian F (weakJet u t)) := Real.sqrt_le_sqrt ht.1

theorem normDensity_measurable (F : ReversibleMetric n) (s : ℝ) (u : SphereLoop n) :
    Measurable (normDensity F s u) :=
  measurable_const.add (measurable_const.mul ((mspeed_measurable F u).div_const _))

theorem normDensity_nonneg (F : ReversibleMetric n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {u : SphereLoop n} (hL : 0 < length F u) (x : ℝ) : 0 ≤ normDensity F s u x :=
  add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 (div_nonneg (mspeed_nonneg F u x) hL.le))

theorem normDensity_integrable (F : ReversibleMetric n) (s : ℝ) (u : SphereLoop n) :
    Integrable (normDensity F s u) intervalMeasure :=
  (integrable_const _).add (((mspeed_integrable F u).div_const _).const_mul _)

theorem normDensity_integrableOn (F : ReversibleMetric n) (s : ℝ) (u : SphereLoop n) :
    IntegrableOn (normDensity F s u) (Ioc 0 1) := by
  show Integrable (normDensity F s u) (volume.restrict (Ioc (0 : ℝ) 1))
  rw [← intervalMeasure_eq]
  exact normDensity_integrable F s u

theorem normDensity_mass (F : ReversibleMetric n) (s : ℝ) {u : SphereLoop n}
    (hL : 0 < length F u) : ∫ x in (0 : ℝ)..1, normDensity F s u x = 1 := by
  have hm : IntervalIntegrable (mspeed F u) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    show Integrable (mspeed F u) (volume.restrict (Ioc (0 : ℝ) 1))
    rw [← intervalMeasure_eq]
    exact mspeed_integrable F u
  unfold normDensity
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hm.div_const _).const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, integral_mspeed, div_self hL.ne']
  simp

theorem normDensity_vanish (F : ReversibleMetric n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {u : SphereLoop n} (hL : 0 < length F u) :
    ∀ᵐ x ∂intervalMeasure, normDensity F s u x = 0 → velocity (u.data : Space n) x = 0 := by
  obtain ⟨k, hk, hkb⟩ := exists_speed_lower F
  filter_upwards [hkb u] with x hx h0
  unfold normDensity at h0
  have h1 : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have h2 : 0 ≤ s * (mspeed F u x / length F u) :=
    mul_nonneg hs.1 (div_nonneg (mspeed_nonneg F u x) hL.le)
  have hs1 : s = 1 := by linarith
  rw [hs1] at h0
  have h3 : mspeed F u x / length F u = 0 := by linarith
  have hm0 : mspeed F u x = 0 := by
    rcases div_eq_zero_iff.mp h3 with h | h
    · exact h
    · exact absurd h hL.ne'
  rw [hm0] at hx
  have hv : ‖velocity (u.data : Space n) x‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg (velocity (u.data : Space n) x)]) (norm_nonneg _)
  exact norm_eq_zero.mp hv

theorem normDensity_finite (F : ReversibleMetric n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {u : SphereLoop n} (hL : 0 < length F u) :
    Integrable (fun x => (normDensity F s u x)⁻¹ * ‖velocity (u.data : Space n) x‖ ^ 2)
      intervalMeasure := by
  obtain ⟨k, hk, hkb⟩ := exists_speed_lower F
  have hbound : Integrable (fun x => 2 * ‖velocity (u.data : Space n) x‖ ^ 2 +
      2 * length F u / k * ‖velocity (u.data : Space n) x‖) intervalMeasure :=
    ((integrable_velocity_sq _).const_mul 2).add ((velocity_integrable _).norm.const_mul _)
  refine hbound.mono' ?_ ?_
  · exact (normDensity_measurable F s u).inv.aemeasurable.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable _).norm.pow 2)
  · filter_upwards [hkb u] with x hx
    have hnn : 0 ≤ (normDensity F s u x)⁻¹ * ‖velocity (u.data : Space n) x‖ ^ 2 :=
      mul_nonneg (inv_nonneg.mpr (normDensity_nonneg F hs hL x)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact inv_density_le hs hL hk (norm_nonneg _) hx

theorem normDensity_admissible (F : ReversibleMetric n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {u : SphereLoop n} (hL : 0 < length F u) : Admissible u (normDensity F s u) where
  measurable := normDensity_measurable F s u
  nonneg := normDensity_nonneg F hs hL
  integrable := normDensity_integrableOn F s u
  mass := normDensity_mass F s hL
  vanish := normDensity_vanish F hs hL
  finite := normDensity_finite F hs hL

/-- The normalization homotopy: identity outside [0, 1] and on loops of length zero. -/
def normLoop (F : ReversibleMetric n) (p : ℝ × SphereLoop n) : SphereLoop n :=
  if h : p.1 ∈ Icc (0 : ℝ) 1 ∧ 0 < length F p.2 then
    reparam p.2 (normDensity F p.1 p.2) (normDensity_admissible F h.1 h.2)
  else p.2

theorem normLoop_of_mem (F : ReversibleMetric n) {p : ℝ × SphereLoop n}
    (h : p.1 ∈ Icc (0 : ℝ) 1 ∧ 0 < length F p.2) :
    normLoop F p = reparam p.2 (normDensity F p.1 p.2) (normDensity_admissible F h.1 h.2) :=
  dite_eq_left h

theorem normLoop_of_not (F : ReversibleMetric n) {p : ℝ × SphereLoop n}
    (h : ¬ (p.1 ∈ Icc (0 : ℝ) 1 ∧ 0 < length F p.2)) : normLoop F p = p.2 :=
  dite_eq_right h

theorem normLoop_of_length_eq_zero (F : ReversibleMetric n) {p : ℝ × SphereLoop n}
    (hL : length F p.2 = 0) : normLoop F p = p.2 :=
  normLoop_of_not F fun h => h.2.ne' hL

theorem speed_ae_eq_zero (F : ReversibleMetric n) {u : SphereLoop n} (hL : length F u = 0) :
    speed F u =ᵐ[intervalMeasure] 0 :=
  (integral_eq_zero_iff_of_nonneg (speed_nonneg F u) (speed_integrable F u)).mp hL

theorem energy_eq_zero_of_length (F : ReversibleMetric n) {u : SphereLoop n}
    (hL : length F u = 0) : SobolevEnergy.energy F u = 0 := by
  unfold SobolevEnergy.energy
  rw [integral_eq_zero_of_ae]
  filter_upwards [speed_ae_eq_zero F hL] with t ht
  rw [← speed_sq, ht]
  simp

theorem representative_normLoop_zero (F : ReversibleMetric n) (p : ℝ × SphereLoop n) :
    continuousRepresentative ((normLoop F p).data : Space n) 0 =
      continuousRepresentative (p.2.data : Space n) 0 := by
  by_cases h : p.1 ∈ Icc (0 : ℝ) 1 ∧ 0 < length F p.2
  · rw [normLoop_of_mem F h, representative_reparam _ ⟨le_rfl, zero_le_one⟩]
    exact (newVal_zero (normDensity_admissible F h.1 h.2))
  · rw [normLoop_of_not F h]

theorem length_normLoop (F : ReversibleMetric n) (p : ℝ × SphereLoop n) :
    length F (normLoop F p) = length F p.2 := by
  by_cases h : p.1 ∈ Icc (0 : ℝ) 1 ∧ 0 < length F p.2
  · rw [normLoop_of_mem F h]
    exact (length_reparam (normDensity_admissible F h.1 h.2)) F
  · rw [normLoop_of_not F h]

/-- The integrand of the normalized energy: F²/((1 − s) + sF/ℓ) a.e. -/
theorem inv_density_mul_lagrangian_ae (F : ReversibleMetric n) (s : ℝ) (u : SphereLoop n) :
    ∀ᵐ x ∂intervalMeasure, (normDensity F s u x)⁻¹ * lagrangian F (weakJet u x) =
      (normDensity F s u x)⁻¹ * mspeed F u x ^ 2 := by
  filter_upwards [mspeed_ae F u] with x hx
  rw [hx, speed_sq]

/-- E(Ψ_s u) ≤ (1 − s) E(u) + s ℓ(u)². -/
theorem energy_normLoop_le (F : ReversibleMetric n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (u : SphereLoop n) :
    SobolevEnergy.energy F (normLoop F (s, u)) ≤ (1 - s) * SobolevEnergy.energy F u + s * length F u ^ 2 := by
  by_cases hL : 0 < length F u
  · have hadm := normDensity_admissible F hs hL
    rw [normLoop_of_mem F (p := (s, u)) ⟨hs, hL⟩, (energy_reparam hadm) F]
    set L := length F u with hLdef
    have hint2 : Integrable (fun x => (1 - s) * lagrangian F (weakJet u x) +
        s * L * mspeed F u x) intervalMeasure :=
      ((density_integrable F u).const_mul _).add ((mspeed_integrable F u).const_mul _)
    have hle : ∫ x, (normDensity F s u x)⁻¹ * lagrangian F (weakJet u x) ∂intervalMeasure ≤
        ∫ x, ((1 - s) * lagrangian F (weakJet u x) + s * L * mspeed F u x) ∂intervalMeasure := by
      apply integral_mono_ae ((inv_mul_density_integrable hadm) F) hint2
      filter_upwards [inv_density_mul_lagrangian_ae F s u, mspeed_ae F u] with x hx hm
      rw [hx]
      have hlag : lagrangian F (weakJet u x) = mspeed F u x ^ 2 := by rw [hm, speed_sq]
      rw [hlag]
      have hσ := Finsler.Normalization.pointwise_energy_bound s (mspeed F u x / L) hs.1 hs.2
        (div_nonneg (mspeed_nonneg F u x) hL.le)
      unfold normDensity
      have hD : 0 ≤ 1 - s + s * (mspeed F u x / L) :=
        add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 (div_nonneg (mspeed_nonneg F u x) hL.le))
      have hmul := mul_le_mul_of_nonneg_left hσ (sq_nonneg L)
      have e1 : L ^ 2 * ((mspeed F u x / L) ^ 2 / (1 - s + s * (mspeed F u x / L))) =
          (1 - s + s * (mspeed F u x / L))⁻¹ * mspeed F u x ^ 2 := by
        field_simp
      have e2 : L ^ 2 * ((1 - s) * (mspeed F u x / L) ^ 2 + s * (mspeed F u x / L)) =
          (1 - s) * mspeed F u x ^ 2 + s * L * mspeed F u x := by
        field_simp
      rw [e1, e2] at hmul
      exact hmul
    have hR : ∫ x, ((1 - s) * lagrangian F (weakJet u x) + s * L * mspeed F u x)
        ∂intervalMeasure = (1 - s) * SobolevEnergy.energy F u + s * L ^ 2 := by
      rw [integral_add ((density_integrable F u).const_mul _) ((mspeed_integrable F u).const_mul _),
        integral_const_mul, integral_const_mul]
      have hm : ∫ x, mspeed F u x ∂intervalMeasure = L := by
        rw [hLdef]
        exact integral_congr_ae (mspeed_ae F u)
      rw [hm]
      unfold SobolevEnergy.energy
      ring
    linarith
  · have hL0 : length F u = 0 := le_antisymm (not_lt.mp hL) (length_nonneg F u)
    rw [normLoop_of_length_eq_zero F (p := (s, u)) hL0, energy_eq_zero_of_length F hL0, hL0]
    simp

/-- The normalization does not increase energy. -/
theorem energy_normLoop_le_energy (F : ReversibleMetric n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (u : SphereLoop n) : SobolevEnergy.energy F (normLoop F (s, u)) ≤ SobolevEnergy.energy F u := by
  have h1 := energy_normLoop_le F hs u
  have h2 := length_sq_le_energy F u
  nlinarith [hs.1, hs.2]

/-- At s = 1 the loop has constant speed: E = ℓ². -/
theorem energy_normLoop_one (F : ReversibleMetric n) {u : SphereLoop n} (hL : 0 < length F u) :
    SobolevEnergy.energy F (normLoop F (1, u)) = length F u ^ 2 := by
  have hs : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hadm := normDensity_admissible F hs hL
  rw [normLoop_of_mem F (p := (1, u)) ⟨hs, hL⟩, (energy_reparam hadm) F]
  set L := length F u with hLdef
  have hcongr : ∀ᵐ x ∂intervalMeasure,
      (normDensity F 1 u x)⁻¹ * lagrangian F (weakJet u x) = L * mspeed F u x := by
    filter_upwards [inv_density_mul_lagrangian_ae F 1 u] with x hx
    rw [hx]
    unfold normDensity
    rw [sub_self, zero_add, one_mul]
    rcases eq_or_lt_of_le (mspeed_nonneg F u x) with h0 | hpos
    · rw [← h0]
      simp
    · field_simp
      exact hLdef.symm
  rw [integral_congr_ae hcongr, integral_const_mul]
  have hm : ∫ x, mspeed F u x ∂intervalMeasure = L := by
    rw [hLdef]
    exact integral_congr_ae (mspeed_ae F u)
  rw [hm]
  ring

/-- The parameter 0 is the identity. -/
theorem normLoop_zero (F : ReversibleMetric n) (u : SphereLoop n) : normLoop F (0, u) = u := by
  by_cases hL : 0 < length F u
  · have hs : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hadm := normDensity_admissible F hs hL
    rw [normLoop_of_mem F (p := (0, u)) ⟨hs, hL⟩]
    have hρ : normDensity F 0 u = fun _ => 1 := by
      funext x
      unfold normDensity
      ring
    have hcumul (y : ℝ) : cumul (normDensity F 0 u) y = y := by
      unfold cumul
      rw [hρ]
      simp
    have htime {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : time (normDensity F 0 u) t = t := by
      have h := (cumul_time hadm) ht
      rwa [hcumul] at h
    apply sphereLoop_data_injective
    apply Finsler.SobolevEnergy.h1_eq_of_representative_eq
    intro t
    change continuousRepresentative ((reparam u (normDensity F 0 u) hadm).data : Space n) t =
      continuousRepresentative (u.data : Space n) t
    rw [representative_reparam hadm t.2, htime t.2]
  · exact normLoop_of_not F fun h => hL h.2

end

end Finsler.NormalizationHomotopy
