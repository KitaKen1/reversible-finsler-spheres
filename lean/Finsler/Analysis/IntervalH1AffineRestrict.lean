module

public import Finsler.Analysis.IntervalH1SpherePath
public import Finsler.Analysis.IntervalH1OfPrimitive
public import Finsler.Geometry.EnergyConservation

/-! Affine restriction of actual weak H¹ graph elements. For 0 ≤ s ≤ t ≤ 1 the composite of
the continuous representative with τ ↦ s + (t − s)τ is again a graph element, whose weak
velocity is (t − s) times the reparametrized velocity. For any density that is quadratic in the
velocity, the integral over the restriction is (t − s) times the integral over [s,t]. For actual
sphere paths the restriction is again a sphere path whose Finsler energy is at most (t − s) E. -/

@[expose] public section

namespace Finsler.SobolevAffine

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevOfPrimitive Finsler.SobolevEnergy Finsler.SobolevSpherePath
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-- The affine parametrization of [s,t] by [0,1]. -/
def aff (s t τ : ℝ) : ℝ := s + (t - s) * τ

theorem aff_zero (s t : ℝ) : aff s t 0 = s := by
  unfold aff
  ring

theorem aff_one (s t : ℝ) : aff s t 1 = t := by
  unfold aff
  ring

theorem aff_mem_Icc {s t τ : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hτ : τ ∈ Icc (0 : ℝ) 1) : aff s t τ ∈ Icc (0 : ℝ) 1 := by
  have h : aff s t τ = (1 - τ) * s + τ * t := by
    unfold aff
    ring
  rw [h]
  have h1 : 0 ≤ 1 - τ := by linarith [hτ.2]
  constructor
  · exact add_nonneg (mul_nonneg h1 hs.1) (mul_nonneg hτ.1 ht.1)
  · have ha : (1 - τ) * s ≤ 1 - τ := mul_le_of_le_one_right h1 hs.2
    have hb : τ * t ≤ τ := mul_le_of_le_one_right hτ.1 ht.2
    linarith

theorem aff_continuous (s t : ℝ) : Continuous (aff s t) := by
  unfold aff
  fun_prop

/-- Affine maps with positive slope push the restricted Lebesgue measure to a constant multiple
of the restricted Lebesgue measure on the image interval. -/
theorem affine_measurePreserving {f : ℝ → ℝ} {c d : ℝ} (hc : 0 < c)
    (hf : ∀ x, f x = d + c * x) {a b a' b' : ℝ} (ha : d + c * a = a') (hb : d + c * b = b') :
    MeasurePreserving f (volume.restrict (Ioo a b))
      (ENNReal.ofReal |c⁻¹| • volume.restrict (Ioo a' b')) := by
  have hfeq : f = fun x => d + c * x := funext hf
  subst hfeq ha hb
  have h1 : MeasurePreserving (fun x : ℝ => c * x) volume (ENNReal.ofReal |c⁻¹| • volume) :=
    ⟨measurable_const_mul _, Real.map_volume_mul_left hc.ne'⟩
  have h2 : MeasurePreserving (fun x : ℝ => d + x) (ENNReal.ofReal |c⁻¹| • volume)
      (ENNReal.ofReal |c⁻¹| • volume) := by
    refine ⟨measurable_const_add d, ?_⟩
    rw [Measure.map_smul, map_add_left_eq_self]
    exact (measurable_const_add d).aemeasurable
  have h3 : MeasurePreserving (fun x : ℝ => d + c * x) volume
      (ENNReal.ofReal |c⁻¹| • volume) := h2.comp h1
  have h4 := h3.restrict_preimage (s := Ioo (d + c * a) (d + c * b)) measurableSet_Ioo
  have hpre : (fun x : ℝ => d + c * x) ⁻¹' Ioo (d + c * a) (d + c * b) = Ioo a b := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [hpre, Measure.restrict_smul] at h4
  exact h4

/-- Composites of L² functions on the unit interval with increasing affine maps onto it. -/
theorem memLp_comp_affine {f : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hf : ∀ x, f x = d + c * x)
    {a b : ℝ} (ha : d + c * a = 0) (hb : d + c * b = 1) (g : ValueLp n) :
    MemLp (fun x => g (f x)) 2 (volume.restrict (Ioo a b)) := by
  have hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)) := Lp.memLp g
  exact (hg.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving
    (affine_measurePreserving hc hf ha hb)

theorem aff_measurePreserving {s t : ℝ} (hst : s < t) :
    MeasurePreserving (aff s t) (volume.restrict (Ioo (0 : ℝ) 1))
      (ENNReal.ofReal |(t - s)⁻¹| • volume.restrict (Ioo s t)) :=
  affine_measurePreserving (sub_pos.mpr hst) (fun _ => rfl) (by ring) (by ring)

/-- The reparametrized continuous representative. -/
def restrRep (u : Space n) (s t τ : ℝ) : Ambient n := continuousRepresentative u (aff s t τ)

/-- The reparametrized weak velocity, scaled by the length of [s,t]. -/
def restrVel (u : Space n) (s t τ : ℝ) : Ambient n := (t - s) • velocity u (aff s t τ)

theorem restrRep_continuousOn (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : ContinuousOn (restrRep u s t) (Icc 0 1) :=
  (continuousRepresentative_continuousOn u).comp (aff_continuous s t).continuousOn
    fun _ hτ => aff_mem_Icc hs ht hτ

theorem velocity_comp_memLp (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hst : s < t) :
    MemLp (fun τ => velocity u (aff s t τ)) 2 intervalMeasure := by
  have hv0 : MemLp (velocity u) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := Lp.memLp (velocity u)
  have hv : MemLp (velocity u) 2 (volume.restrict (Ioo s t)) :=
    hv0.mono_measure (Measure.restrict_mono (Ioo_subset_Ioo hs.1 ht.2) le_rfl)
  have hv' := hv.smul_measure (c := ENNReal.ofReal |(t - s)⁻¹|) ENNReal.ofReal_ne_top
  exact hv'.comp_measurePreserving (aff_measurePreserving hst)

theorem restrVel_memLp (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) : MemLp (restrVel u s t) 2 intervalMeasure := by
  rcases hst.lt_or_eq with hlt | heq
  · exact (velocity_comp_memLp u hs ht hlt).const_smul (t - s)
  · have hz : restrVel u s t = fun _ => 0 := by
      funext τ
      simp [restrVel, heq]
    rw [hz]
    exact MemLp.zero

theorem integral_restrVel (u : Space n) (s t τ : ℝ) :
    ∫ σ in (0 : ℝ)..τ, restrVel u s t σ = ∫ x in aff s t 0..aff s t τ, velocity u x := by
  simp only [restrVel]
  rw [intervalIntegral.integral_smul]
  exact intervalIntegral.smul_integral_comp_add_mul (fun x => velocity u x) (t - s) s

theorem restrRep_eq_add_integral (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    restrRep u s t τ = restrRep u s t 0 + ∫ σ in (0 : ℝ)..τ, restrVel u s t σ := by
  have h0 := aff_mem_Icc hs ht (left_mem_Icc.mpr zero_le_one)
  have hτ' := aff_mem_Icc hs ht hτ
  have hsub := continuousRepresentative_sub u h0 hτ'
  rw [integral_restrVel, ← hsub]
  unfold restrRep
  abel

/-- The affine restriction of a graph element to [s,t], parametrized by [0,1]. -/
def restrict (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≤ t) : Space n :=
  ofPrimitive (restrRep_continuousOn u hs ht) (restrVel_memLp u hs ht hst)
    (fun _ hτ => restrRep_eq_add_integral u hs ht hτ)

section Restrict

variable (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
  (hst : s ≤ t)

theorem representative_restrict {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (restrict u hs ht hst) τ = continuousRepresentative u (aff s t τ) :=
  representative_ofPrimitive _ _ _ hτ

theorem representative_restrict_zero :
    continuousRepresentative (restrict u hs ht hst) 0 = continuousRepresentative u s := by
  rw [representative_restrict u hs ht hst (left_mem_Icc.mpr zero_le_one), aff_zero]

theorem representative_restrict_one :
    continuousRepresentative (restrict u hs ht hst) 1 = continuousRepresentative u t := by
  rw [representative_restrict u hs ht hst (right_mem_Icc.mpr zero_le_one), aff_one]

theorem velocity_restrict_ae :
    velocity (restrict u hs ht hst) =ᵐ[intervalMeasure] restrVel u s t :=
  velocity_ofPrimitive_ae _ _ _

/-- Change of variables for densities quadratic in the velocity. -/
theorem integral_restrict_of_quadratic (G : Ambient n × Ambient n → ℝ)
    (hG : ∀ q v : Ambient n, ∀ r : ℝ, G (q, r • v) = r ^ 2 * G (q, v)) :
    ∫ τ, G (continuousRepresentative (restrict u hs ht hst) τ,
        velocity (restrict u hs ht hst) τ) ∂intervalMeasure =
      (t - s) * ∫ x in s..t, G (continuousRepresentative u x, velocity u x) := by
  set g : ℝ → ℝ := fun x => G (continuousRepresentative u x, velocity u x) with hg
  have hae : (fun τ => G (continuousRepresentative (restrict u hs ht hst) τ,
      velocity (restrict u hs ht hst) τ)) =ᵐ[intervalMeasure]
      fun τ => (t - s) ^ 2 * g (s + (t - s) * τ) := by
    have hmem : ∀ᵐ τ ∂intervalMeasure, τ ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    filter_upwards [velocity_restrict_ae u hs ht hst, hmem] with τ hv hτ
    rw [representative_restrict u hs ht hst (Ioo_subset_Icc_self hτ), hv]
    exact hG _ _ _
  rw [integral_congr_ae hae]
  change ∫ τ in Ioo (0 : ℝ) 1, (t - s) ^ 2 * g (s + (t - s) * τ) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul]
  have hcv := intervalIntegral.smul_integral_comp_add_mul g (t - s) s (a := 0) (b := 1)
  rw [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at hcv
  rw [← hcv]
  ring

end Restrict

theorem pathEnergy_restrict (F : ReversibleMetric n) (u : Space n) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    pathEnergy F (restrict u hs ht hst) =
      (t - s) * ∫ x in s..t, lagrangian F (continuousRepresentative u x, velocity u x) :=
  integral_restrict_of_quadratic u hs ht hst (lagrangian F)
    (Finsler.EnergyConservation.lagrangian_velocity_smul F)

theorem restrict_mem {w : Space n} (hw : w ∈ SpherePath n) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    restrict w hs ht hst ∈ SpherePath n := by
  intro τ hτ
  rw [representative_restrict w hs ht hst hτ]
  exact hw _ (aff_mem_Icc hs ht hτ)

/-- Sampling estimate in energy form: the restriction of a sphere path to [s,t] has energy at
most (t − s) E. -/
theorem pathEnergy_restrict_le (F : ReversibleMetric n) {w : Space n} (hw : w ∈ SpherePath n)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    pathEnergy F (restrict w hs ht hst) ≤ (t - s) * pathEnergy F w := by
  rw [pathEnergy_restrict, pathEnergy_eq_intervalIntegral F w]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hst)
  exact intervalIntegral.integral_mono_interval hs.1 hst ht.2
    (Eventually.of_forall fun x => sq_nonneg _) (density_intervalIntegrable F hw)

/-- For actual sphere loops: the restriction to [s,t] has energy at most (t − s) E. -/
theorem pathEnergy_restrict_loop_le (F : ReversibleMetric n) (u : SphereLoop n) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    pathEnergy F (restrict (u.data : Space n) hs ht hst) ≤ (t - s) * energy F u :=
  pathEnergy_restrict_le F (sphereLoop_mem u) hs ht hst

end

end Finsler.SobolevAffine
