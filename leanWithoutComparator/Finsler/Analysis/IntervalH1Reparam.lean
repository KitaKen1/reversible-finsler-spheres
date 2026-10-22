module

public import Finsler.Analysis.IntervalH1Length
public import Finsler.Analysis.IntervalH1OfPrimitive
public import Finsler.Analysis.IntervalH1EnergyZero
public import Finsler.Analysis.IntervalH1VariationContinuity
public import Finsler.Geometry.EnergyConservation
public import Finsler.Analysis.MonotoneSubst

/-! Reparametrization of H¹ sphere loops by a density. For a nonnegative density ρ of total
mass one that vanishes only where the velocity vanishes, with ∫ ‖u̇‖²/ρ finite, let φ be its
primitive and ψ the largest point below a value. The loop u ∘ ψ is the primitive of
(u̇/ρ) ∘ ψ: the primitive of u̇ up to ψ t is that of ρ · (u̇/ρ), and substitution along φ turns
it into the primitive of (u̇/ρ) ∘ ψ up to φ (ψ t) = t. Substitution also gives the energy
∫ F²(u,u̇)/ρ, the squared velocity norm ∫ ‖u̇‖²/ρ, and the length, which is unchanged. -/

@[expose] public section

namespace Finsler.SobolevReparam

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevEnergy Finsler.SobolevOfPrimitive Finsler.MonotoneSubst Finsler.SobolevLength
open Finsler.SobolevEnergyDifferential
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

theorem intervalMeasure_eq : intervalMeasure = volume.restrict (Ioc (0 : ℝ) 1) := by
  change volume.restrict (Ioo (0 : ℝ) 1) = _
  exact Measure.restrict_congr_set Ioo_ae_eq_Ioc

/-- Densities admissible for reparametrizing the loop u. -/
structure Admissible (u : SphereLoop n) (ρ : ℝ → ℝ) : Prop where
  measurable : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  integrable : IntegrableOn ρ (Ioc 0 1)
  mass : ∫ x in (0 : ℝ)..1, ρ x = 1
  vanish : ∀ᵐ x ∂intervalMeasure, ρ x = 0 → velocity (u.data : Space n) x = 0
  finite : Integrable (fun x => (ρ x)⁻¹ * ‖velocity (u.data : Space n) x‖ ^ 2) intervalMeasure

/-- The primitive of the density. -/
def cumul (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, ρ y

/-- The new time: the largest point at which the primitive is at most t. -/
def time (ρ : ℝ → ℝ) (t : ℝ) : ℝ := rinv (cumul ρ) t

/-- The velocity divided by the density. -/
def scaledVel (u : SphereLoop n) (ρ : ℝ → ℝ) (x : ℝ) : Ambient n :=
  (ρ x)⁻¹ • velocity (u.data : Space n) x

/-- The reparametrized values. -/
def newVal (u : SphereLoop n) (ρ : ℝ → ℝ) (t : ℝ) : Ambient n :=
  continuousRepresentative (u.data : Space n) (time ρ t)

/-- The reparametrized velocity. -/
def newVel (u : SphereLoop n) (ρ : ℝ → ℝ) (t : ℝ) : Ambient n := scaledVel u ρ (time ρ t)

variable {u : SphereLoop n} {ρ : ℝ → ℝ}

theorem cumul_zero : cumul ρ 0 = 0 := intervalIntegral.integral_same

theorem admissible_isPrimitive (hρ : Admissible u ρ) : IsPrimitive ρ (cumul ρ) 0 1 where
  le := zero_le_one
  nonneg := hρ.nonneg
  integrable := hρ.integrable
  eq x _ := by rw [cumul_zero, zero_add]; rfl

theorem cumul_one (hρ : Admissible u ρ) : cumul ρ 1 = 1 := hρ.mass

theorem time_mem (t : ℝ) : time ρ t ∈ Icc (0 : ℝ) 1 := rinv_mem t

theorem cumul_time (hρ : Admissible u ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cumul ρ (time ρ t) = t :=
  map_rinv (primitive_continuousOn (admissible_isPrimitive hρ)) cumul_zero (cumul_one hρ) ht

theorem time_one (hρ : Admissible u ρ) : time ρ 1 = 1 := by
  have h := le_rinv (φ := cumul ρ) (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  rw [(cumul_one hρ)] at h
  exact le_antisymm (time_mem 1).2 h

theorem smul_scaledVel_ae (hρ : Admissible u ρ) :
    ∀ᵐ x ∂intervalMeasure, ρ x • scaledVel u ρ x = velocity (u.data : Space n) x := by
  filter_upwards [hρ.vanish] with x hx
  unfold scaledVel
  by_cases h0 : ρ x = 0
  · rw [h0, zero_smul, hx h0]
  · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem scaledVel_stronglyMeasurable (hρ : Admissible u ρ) :
    StronglyMeasurable (scaledVel u ρ) :=
  hρ.measurable.inv.stronglyMeasurable.smul (Lp.stronglyMeasurable _)

theorem newVel_stronglyMeasurable (hρ : Admissible u ρ) :
    StronglyMeasurable (newVel u ρ) :=
  (scaledVel_stronglyMeasurable hρ).comp_measurable rinv_measurable

theorem lintegral_comp_time (hρ : Admissible u ρ) {H : ℝ → ℝ≥0∞}
    (hH : AEMeasurable (fun t => H (time ρ t)) intervalMeasure) :
    ∫⁻ t, H (time ρ t) ∂intervalMeasure = ∫⁻ x, ENNReal.ofReal (ρ x) * H x ∂intervalMeasure := by
  rw [intervalMeasure_eq] at hH ⊢
  exact lintegral_comp_rinv (admissible_isPrimitive hρ) cumul_zero (cumul_one hρ) hH

theorem mul_inv_sq_mul (a b : ℝ) : a * ((a⁻¹) ^ 2 * b) = a⁻¹ * b := by
  rcases eq_or_ne a 0 with h | h
  · rw [h, inv_zero]
    ring
  · field_simp

theorem ofReal_mul_scaledVel_sq (hρ : Admissible u ρ) (x : ℝ) :
    ENNReal.ofReal (ρ x) * ENNReal.ofReal (‖scaledVel u ρ x‖ ^ 2) =
      ENNReal.ofReal ((ρ x)⁻¹ * ‖velocity (u.data : Space n) x‖ ^ 2) := by
  rw [← ENNReal.ofReal_mul (hρ.nonneg x)]
  congr 1
  unfold scaledVel
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact mul_inv_sq_mul _ _

theorem lintegral_newVel_sq (hρ : Admissible u ρ) :
    ∫⁻ t, ENNReal.ofReal (‖newVel u ρ t‖ ^ 2) ∂intervalMeasure =
      ∫⁻ x, ENNReal.ofReal ((ρ x)⁻¹ * ‖velocity (u.data : Space n) x‖ ^ 2) ∂intervalMeasure := by
  have hm : AEMeasurable (fun t => ENNReal.ofReal (‖scaledVel u ρ (time ρ t)‖ ^ 2))
      intervalMeasure :=
    ((((scaledVel_stronglyMeasurable hρ).measurable.norm.pow_const 2).ennreal_ofReal).comp
      rinv_measurable).aemeasurable
  change ∫⁻ t, ENNReal.ofReal (‖scaledVel u ρ (time ρ t)‖ ^ 2) ∂intervalMeasure = _
  rw [lintegral_comp_time (H := fun x => ENNReal.ofReal (‖scaledVel u ρ x‖ ^ 2)) hρ hm]
  exact lintegral_congr fun x => ofReal_mul_scaledVel_sq hρ x

theorem newVel_memLp (hρ : Admissible u ρ) : MemLp (newVel u ρ) 2 intervalMeasure := by
  have hm : AEStronglyMeasurable (newVel u ρ) intervalMeasure :=
    (newVel_stronglyMeasurable hρ).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _),
    (lintegral_newVel_sq hρ)]
  have hfin := hρ.finite.hasFiniteIntegral
  rwa [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
    mul_nonneg (inv_nonneg.mpr (hρ.nonneg x)) (sq_nonneg _))] at hfin

theorem newVel_integrableOn (hρ : Admissible u ρ) :
    IntegrableOn (newVel u ρ) (Ioc 0 1) := by
  have h := (newVel_memLp hρ).integrable (by norm_num)
  rw [intervalMeasure_eq] at h
  exact h

/-- The increments of the reparametrized values are primitives of the reparametrized
velocity. -/
theorem newVal_sub (hρ : Admissible u ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ y in (0 : ℝ)..t, newVel u ρ y =
      continuousRepresentative (u.data : Space n) (time ρ t) -
        continuousRepresentative (u.data : Space n) 0 := by
  have hb := time_mem (ρ := ρ) t
  have h1 := continuousRepresentative_sub (u.data : Space n) ⟨le_rfl, zero_le_one⟩ hb
  have h2 : ∫ x in (0 : ℝ)..(time ρ t), velocity (u.data : Space n) x =
      ∫ x in (0 : ℝ)..(time ρ t), ρ x • scaledVel u ρ x := by
    apply intervalIntegral.integral_congr_ae
    have hae' : ∀ᵐ x ∂volume, x ∈ Ioo (0 : ℝ) 1 →
        ρ x • scaledVel u ρ x = velocity (u.data : Space n) x :=
      (ae_restrict_iff' measurableSet_Ioo).mp (smul_scaledVel_ae hρ)
    have hne : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by
      rw [ae_iff]
      simp
    filter_upwards [hae', hne] with x hx hx1 hxI
    rw [uIoc_of_le hb.1] at hxI
    exact (hx ⟨hxI.1, lt_of_le_of_ne (hxI.2.trans hb.2) hx1⟩).symm
  have hint : IntegrableOn (fun y => scaledVel u ρ (rinv (cumul ρ) y)) (Ioc 0 t) :=
    (newVel_integrableOn hρ).mono_set (Ioc_subset_Ioc le_rfl ht.2)
  have h3 := integral_comp_rinv (admissible_isPrimitive hρ) cumul_zero (cumul_one hρ) ht hint
  rw [h1, h2]
  exact h3

/-- The reparametrized values are the primitive of the reparametrized velocity. -/
theorem newVal_eq (hρ : Admissible u ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    newVal u ρ t =
      continuousRepresentative (u.data : Space n) 0 + ∫ y in (0 : ℝ)..t, newVel u ρ y := by
  rw [(newVal_sub hρ) ht]
  show continuousRepresentative (u.data : Space n) (time ρ t) = _
  abel

theorem newVal_zero (hρ : Admissible u ρ) :
    newVal u ρ 0 = continuousRepresentative (u.data : Space n) 0 :=
  sub_eq_zero.mp (((newVal_sub hρ) ⟨le_rfl, zero_le_one⟩).symm.trans intervalIntegral.integral_same)

theorem newVal_prim (hρ : Admissible u ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    newVal u ρ t = newVal u ρ 0 + ∫ y in (0 : ℝ)..t, newVel u ρ y := by
  rw [(newVal_zero hρ)]
  exact (newVal_eq hρ) ht

theorem newVal_continuousOn (hρ : Admissible u ρ) :
    ContinuousOn (newVal u ρ) (Icc 0 1) := by
  have hint : IntegrableOn (newVel u ρ) (uIcc 0 1) volume := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr (newVel_integrableOn hρ)
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) hint
  rw [uIcc_of_le zero_le_one] at hc
  exact (continuousOn_const.add hc).congr fun t ht => (newVal_eq hρ) ht

theorem newVal_one (hρ : Admissible u ρ) : newVal u ρ 1 = newVal u ρ 0 := by
  rw [(newVal_zero hρ)]
  unfold newVal
  rw [(time_one hρ)]
  exact (mem_periodicSubmodule_iff (u.data : Space n)).mp u.data.property

/-- The reparametrized graph element. -/
def reparamData (hρ : Admissible u ρ) : Space n :=
  ofPrimitive (newVal_continuousOn hρ) (newVel_memLp hρ) (fun _ ht => (newVal_prim hρ) ht)

theorem reparamData_periodic (hρ : Admissible u ρ) : reparamData hρ ∈ periodicSubmodule n :=
  ofPrimitive_periodic _ _ _ (newVal_one hρ)

/-- The reparametrized sphere loop. -/
def reparam (u : SphereLoop n) (ρ : ℝ → ℝ) (hρ : Admissible u ρ) : SphereLoop n :=
  ⟨⟨reparamData hρ, reparamData_periodic hρ⟩, fun t => by
    change ‖continuousRepresentative (reparamData hρ) t‖ = 1
    rw [reparamData, representative_ofPrimitive (newVal_continuousOn hρ) (newVel_memLp hρ)
      (fun _ ht => (newVal_prim hρ) ht) t.2]
    exact u.sphere_constraint ⟨time ρ t, time_mem t⟩⟩

theorem representative_reparam (hρ : Admissible u ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative ((reparam u ρ hρ).data : Space n) t =
      continuousRepresentative (u.data : Space n) (time ρ t) :=
  representative_ofPrimitive (newVal_continuousOn hρ) (newVel_memLp hρ)
    (fun _ ht => (newVal_prim hρ) ht) ht

theorem velocity_reparam_ae (hρ : Admissible u ρ) :
    velocity ((reparam u ρ hρ).data : Space n) =ᵐ[intervalMeasure] newVel u ρ :=
  velocity_ofPrimitive_ae (newVal_continuousOn hρ) (newVel_memLp hρ)
    (fun _ ht => (newVal_prim hρ) ht)

theorem reparam_weakJet_ae (hρ : Admissible u ρ) :
    ∀ᵐ t ∂intervalMeasure, weakJet (reparam u ρ hρ) t =
      (continuousRepresentative (u.data : Space n) (time ρ t), scaledVel u ρ (time ρ t)) := by
  filter_upwards [velocity_reparam_ae hρ, ae_restrict_mem measurableSet_Ioo] with t hv ht
  change (continuousRepresentative ((reparam u ρ hρ).data : Space n) t,
    velocity ((reparam u ρ hρ).data : Space n) t) = _
  rw [representative_reparam hρ (Ioo_subset_Icc_self ht), hv]
  rfl

/-- Lower integrals of functions of the jet transform by the density. -/
theorem reparam_lintegral_jet (hρ : Admissible u ρ) {G : Ambient n × Ambient n → ℝ≥0∞}
    (hG : AEMeasurable (fun t => G (weakJet (reparam u ρ hρ) t)) intervalMeasure) :
    ∫⁻ t, G (weakJet (reparam u ρ hρ) t) ∂intervalMeasure =
      ∫⁻ x, ENNReal.ofReal (ρ x) *
        G (continuousRepresentative (u.data : Space n) x, scaledVel u ρ x) ∂intervalMeasure := by
  have hae := (reparam_weakJet_ae hρ)
  have h1 : ∫⁻ t, G (weakJet (reparam u ρ hρ) t) ∂intervalMeasure =
      ∫⁻ t, G (continuousRepresentative (u.data : Space n) (time ρ t), scaledVel u ρ (time ρ t))
        ∂intervalMeasure := lintegral_congr_ae (hae.mono fun t ht => congrArg G ht)
  rw [h1]
  apply lintegral_comp_time
    (H := fun x => G (continuousRepresentative (u.data : Space n) x, scaledVel u ρ x)) hρ
  exact hG.congr (hae.mono fun t ht => congrArg G ht)

theorem inv_mul_density_integrable (hρ : Admissible u ρ) (F : ReversibleMetric n) :
    Integrable (fun x => (ρ x)⁻¹ * lagrangian F (weakJet u x)) intervalMeasure := by
  obtain ⟨c, C, _hc, _hC, hb⟩ := exists_density_bounds F
  refine (hρ.finite.const_mul C).mono' ?_ ?_
  · exact hρ.measurable.inv.aemeasurable.aestronglyMeasurable.mul
      (density_aestronglyMeasurable F u)
  · filter_upwards [hb u] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (hρ.nonneg x))
      (density_nonneg F u x))]
    calc (ρ x)⁻¹ * lagrangian F (weakJet u x)
        ≤ (ρ x)⁻¹ * (C * ‖velocity (u.data : Space n) x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hx.2 (inv_nonneg.mpr (hρ.nonneg x))
      _ = C * ((ρ x)⁻¹ * ‖velocity (u.data : Space n) x‖ ^ 2) := by ring

/-- The energy of the reparametrized loop. -/
theorem energy_reparam (hρ : Admissible u ρ) (F : ReversibleMetric n) :
    SobolevEnergy.energy F (reparam u ρ hρ) =
      ∫ x, (ρ x)⁻¹ * lagrangian F (weakJet u x) ∂intervalMeasure := by
  unfold SobolevEnergy.energy
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => density_nonneg F _ t)
      (density_aestronglyMeasurable F _),
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
      mul_nonneg (inv_nonneg.mpr (hρ.nonneg x)) (density_nonneg F u x))
      ((inv_mul_density_integrable hρ) F).aestronglyMeasurable]
  congr 1
  rw [reparam_lintegral_jet (G := fun z => ENNReal.ofReal (lagrangian F z)) hρ
    (density_aestronglyMeasurable F _).aemeasurable.ennreal_ofReal]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (hρ.nonneg x)]
  congr 1
  unfold scaledVel
  rw [EnergyConservation.lagrangian_velocity_smul]
  exact mul_inv_sq_mul _ _

/-- The squared velocity norm of the reparametrized loop. -/
theorem reparam_velocity_norm_sq (hρ : Admissible u ρ) :
    ‖velocity ((reparam u ρ hρ).data : Space n)‖ ^ 2 =
      ∫ x, (ρ x)⁻¹ * ‖velocity (u.data : Space n) x‖ ^ 2 ∂intervalMeasure := by
  rw [lp_two_norm_eq_sqrt_integral_norm_sq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  have hv := Lp.aestronglyMeasurable (velocity ((reparam u ρ hρ).data : Space n))
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      (hv.norm.pow 2),
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
      mul_nonneg (inv_nonneg.mpr (hρ.nonneg x)) (sq_nonneg _)) hρ.finite.aestronglyMeasurable]
  congr 1
  rw [← (lintegral_newVel_sq hρ)]
  apply lintegral_congr_ae
  filter_upwards [velocity_reparam_ae hρ] with t ht
  rw [ht]

/-- Reparametrization preserves length. -/
theorem length_reparam (hρ : Admissible u ρ) (F : ReversibleMetric n) :
    length F (reparam u ρ hρ) = length F u := by
  unfold length speed
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
      (density_aestronglyMeasurable F _).aemeasurable.sqrt.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
      (density_aestronglyMeasurable F u).aemeasurable.sqrt.aestronglyMeasurable]
  congr 1
  rw [reparam_lintegral_jet (G := fun z => ENNReal.ofReal (Real.sqrt (lagrangian F z))) hρ
    (density_aestronglyMeasurable F _).aemeasurable.sqrt.ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [hρ.vanish] with x hx
  rw [← ENNReal.ofReal_mul (hρ.nonneg x)]
  congr 1
  unfold scaledVel
  rw [EnergyConservation.lagrangian_velocity_smul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (inv_nonneg.mpr (hρ.nonneg x))]
  rcases eq_or_ne (ρ x) 0 with h0 | h0
  · have hz := hx h0
    have h0q : lagrangian F (continuousRepresentative (u.data : Space n) x, 0) = 0 := by
      have h := EnergyConservation.lagrangian_velocity_smul F
        (continuousRepresentative (u.data : Space n) x) 0 0
      simpa using h
    have hL : lagrangian F (continuousRepresentative (u.data : Space n) x,
        velocity (u.data : Space n) x) = 0 := by
      rw [hz]
      exact h0q
    change ρ x * ((ρ x)⁻¹ * Real.sqrt (lagrangian F (continuousRepresentative (u.data : Space n) x,
      velocity (u.data : Space n) x))) = Real.sqrt (lagrangian F
      (continuousRepresentative (u.data : Space n) x, velocity (u.data : Space n) x))
    simp only [hL, Real.sqrt_zero, mul_zero]
  · exact mul_inv_cancel_left₀ h0 _

end

end Finsler.SobolevReparam
