module

public import Finsler.Analysis.SmoothSobolev
public import Mathlib.MeasureTheory.Group.Integral

/-! Reflection on the actual weak H¹ graph and periodic sphere interval model.
The reflected weak derivative is certified through the already proved velocity
primitive and interval change of variables. No classical-a.e. derivative is
substituted for the distributional derivative. -/

@[expose] public section

namespace Finsler.SobolevReverse

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.Geometry
open Finsler.SobolevEnergy MeasureTheory Set Filter
open scoped Topology

noncomputable section

def reflection (t : ℝ) : ℝ := 1 - t

theorem reflection_involutive : Function.Involutive reflection := by
  intro t
  change 1 - (1 - t) = t
  ring

theorem reflection_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 1) : reflection t ∈ Icc 0 1 := by
  change 0 ≤ 1 - t ∧ 1 - t ≤ 1
  constructor <;> linarith [ht.1, ht.2]

theorem reflection_preimage_Ioo : reflection ⁻¹' Ioo (0 : ℝ) 1 = Ioo 0 1 := by
  ext t
  change (0 < 1 - t ∧ 1 - t < 1) ↔ (0 < t ∧ t < 1)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem reflection_measurePreserving :
    MeasurePreserving reflection intervalMeasure intervalMeasure := by
  have h := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
  change MeasurePreserving reflection (volume.restrict (reflection ⁻¹' Ioo (0 : ℝ) 1))
    (volume.restrict (Ioo (0 : ℝ) 1)) at h
  rw [reflection_preimage_Ioo] at h
  exact h

def reflectLpL (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Lp H 2 intervalMeasure →L[ℝ] Lp H 2 intervalMeasure :=
  (Lp.compMeasurePreservingₗᵢ ℝ reflection reflection_measurePreserving).toContinuousLinearMap

theorem reflectLpL_ae {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : Lp H 2 intervalMeasure) :
    reflectLpL H f =ᵐ[intervalMeasure] fun t => f (reflection t) :=
  Lp.coeFn_compMeasurePreserving f reflection_measurePreserving

theorem reflectLpL_norm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : Lp H 2 intervalMeasure) : ‖reflectLpL H f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f reflection_measurePreserving

theorem reflectLpL_involutive {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : Lp H 2 intervalMeasure) : reflectLpL H (reflectLpL H f) = f := by
  apply Lp.ext
  filter_upwards [reflectLpL_ae (reflectLpL H f),
    reflection_measurePreserving.quasiMeasurePreserving.ae_eq_comp (reflectLpL_ae f)] with t h₁ h₂
  exact h₁.trans (by simpa only [Function.comp_apply, reflection_involutive t] using h₂)

def reverseValue {n : ℕ} (u : Space n) : ValueLp n := reflectLpL (Ambient n) (value u)

def reverseDerivative {n : ℕ} (u : Space n) : DerivativeLp n :=
  -reflectLpL (ℝ →L[ℝ] Ambient n) (derivative u)

def reverseVelocityFun {n : ℕ} (u : Space n) (t : ℝ) : Ambient n :=
  -velocity u (reflection t)

theorem reverseVelocityFun_memLp {n : ℕ} (u : Space n) :
    MemLp (reverseVelocityFun u) 2 intervalMeasure :=
  ((Lp.memLp (velocity u)).comp_measurePreserving reflection_measurePreserving).neg

theorem reverseVelocityFun_intervalIntegrable {n : ℕ} (u : Space n) :
    IntervalIntegrable (reverseVelocityFun u) volume 0 1 := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact (reverseVelocityFun_memLp u).integrable (by norm_num)

theorem reverseValue_ae {n : ℕ} (u : Space n) :
    reverseValue u =ᵐ[intervalMeasure] fun t => continuousRepresentative u (reflection t) :=
  (reflectLpL_ae (value u)).trans
    (reflection_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (value_ae_continuousRepresentative u))

theorem reverseDerivative_apply_ae {n : ℕ} (u : Space n) (d : ℝ) :
    (fun t => reverseDerivative u t d) =ᵐ[intervalMeasure]
      fun t => d • reverseVelocityFun u t := by
  filter_upwards [Lp.coeFn_neg (reflectLpL (ℝ →L[ℝ] Ambient n) (derivative u)),
    reflectLpL_ae (derivative u),
    reflection_measurePreserving.quasiMeasurePreserving.ae (velocity_apply_ae u)] with t hn hD hv
  change (-reflectLpL (ℝ →L[ℝ] Ambient n) (derivative u)) t d =
    d • (-velocity u (reflection t))
  rw [hn]
  change (-(reflectLpL (ℝ →L[ℝ] Ambient n) (derivative u) t)) d =
    d • (-velocity u (reflection t))
  rw [hD]
  simp only [neg_apply]
  have hlin : derivative u (reflection t) d = d • derivative u (reflection t) 1 := by
    simpa only [smul_eq_mul, mul_one] using (derivative u (reflection t)).map_smul d 1
  rw [hlin, ← hv, smul_neg]

theorem reverse_primitive_identity {n : ℕ} (u : Space n) {t : ℝ} (ht : t ∈ Icc 0 1) :
    continuousRepresentative u (reflection t) = continuousRepresentative u 1 +
      Finsler.IntervalPrimitive.primitive (reverseVelocityFun u) t := by
  have hinc := continuousRepresentative_sub u (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    (reflection_mem_Icc ht)
  have hP : Finsler.IntervalPrimitive.primitive (reverseVelocityFun u) t =
      ∫ x in (1 : ℝ)..reflection t, velocity u x := by
    change (∫ x in (0 : ℝ)..t, -velocity u (1 - x)) = _
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left]
    simp only [sub_zero]
    exact (intervalIntegral.integral_symm (1 - t) 1).symm
  rw [hP]
  exact (sub_eq_iff_eq_add.mp hinc).trans (add_comm _ _)

theorem reverseValue_hasWeakLineVelocity {n : ℕ} (u : Space n) :
    TauCeti.HasWeakLineDerivOn volume unitInterval (reverseValue u) (reverseVelocityFun u) 1 := by
  have hp := Finsler.IntervalPrimitive.primitive_hasWeakLineDeriv
    (reverseVelocityFun_intervalIntegrable u)
  have hc : TauCeti.HasWeakLineDerivOn volume unitInterval
      (fun _ : ℝ => continuousRepresentative u 1) (fun _ => (0 : Ambient n)) 1 :=
    TauCeti.hasWeakLineDerivOn_const _
  have hs := hc.add hp
  change TauCeti.HasWeakLineDerivOn volume unitInterval
    (fun t => continuousRepresentative u 1 +
      Finsler.IntervalPrimitive.primitive (reverseVelocityFun u) t)
    (fun t => 0 + reverseVelocityFun u t) 1 at hs
  have hz : (fun t => (0 : Ambient n) + reverseVelocityFun u t) = reverseVelocityFun u := by
    funext t
    exact zero_add _
  rw [hz] at hs
  have he : reverseValue u =ᵐ[intervalMeasure]
      fun t => continuousRepresentative u 1 +
        Finsler.IntervalPrimitive.primitive (reverseVelocityFun u) t := by
    filter_upwards [reverseValue_ae u, ae_restrict_mem measurableSet_Ioo] with t hu ht
    exact hu.trans (reverse_primitive_identity u (Ioo_subset_Icc_self ht))
  have hs' : TauCeti.HasWeakLineDerivOn volume unitInterval
      (fun t => continuousRepresentative u 1 +
        Finsler.IntervalPrimitive.primitive (reverseVelocityFun u) t) (reverseVelocityFun u) 1 := by
    exact hs
  exact hs'.congr_ae he.symm

theorem reverseValue_hasWeakFDeriv {n : ℕ} (u : Space n) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (reverseValue u))
      (reverseDerivative u) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have hs : TauCeti.HasWeakLineDerivOn volume unitInterval (reverseValue u)
      (fun t => d • reverseVelocityFun u t) d := by
    have h := (reverseValue_hasWeakLineVelocity u).smul_direction d
    change TauCeti.HasWeakLineDerivOn volume unitInterval (reverseValue u)
      (fun t => d • reverseVelocityFun u t) (d • (1 : ℝ)) at h
    simpa only [smul_eq_mul, mul_one] using h
  exact hs.congr_ae_deriv (reverseDerivative_apply_ae u d).symm

def reverseData {n : ℕ} (u : Space n) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (reverseValue u) (reverseDerivative u)
    (reverseValue_hasWeakFDeriv u)

theorem value_reverseData {n : ℕ} (u : Space n) : value (reverseData u) = reverseValue u := by
  change TauCeti.WeakDerivStep.prevL (base n) (reverseData u) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_reverseData {n : ℕ} (u : Space n) :
    derivative (reverseData u) = reverseDerivative u := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (reverseData u) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem velocity_reverseData_ae {n : ℕ} (u : Space n) :
    velocity (reverseData u) =ᵐ[intervalMeasure] reverseVelocityFun u := by
  have h := reverseDerivative_apply_ae u 1
  rw [← derivative_reverseData] at h
  exact (velocity_apply_ae (reverseData u)).trans (by simpa only [one_smul] using h)

theorem representative_reverseData {n : ℕ} (u : Space n) {t : ℝ} (ht : t ∈ Icc 0 1) :
    continuousRepresentative (reverseData u) t = continuousRepresentative u (reflection t) := by
  have hq : ContinuousOn (fun t => continuousRepresentative u (reflection t)) (Icc 0 1) :=
    (continuousRepresentative_continuousOn u).comp
      (continuous_const.sub continuous_id).continuousOn (fun _ hs => reflection_mem_Icc hs)
  have hv : value (reverseData u) =ᵐ[intervalMeasure]
      fun t => continuousRepresentative u (reflection t) := by
    rw [value_reverseData]
    exact reverseValue_ae u
  exact continuous_representative_unique (continuousRepresentative_continuousOn _) hq
    (value_ae_continuousRepresentative _) hv ht


theorem value_reverseData_norm {n : ℕ} (u : Space n) :
    ‖value (reverseData u)‖ = ‖value u‖ := by
  rw [value_reverseData]
  exact reflectLpL_norm _

theorem derivative_reverseData_norm {n : ℕ} (u : Space n) :
    ‖derivative (reverseData u)‖ = ‖derivative u‖ := by
  rw [derivative_reverseData]
  change ‖-reflectLpL (ℝ →L[ℝ] Ambient n) (derivative u)‖ = _
  rw [norm_neg]
  exact reflectLpL_norm _

theorem velocity_reverseData_norm {n : ℕ} (u : Space n) :
    ‖velocity (reverseData u)‖ = ‖velocity u‖ := by
  rw [velocity_norm_eq, derivative_reverseData_norm, velocity_norm_eq]

theorem reverseData_norm {n : ℕ} (u : Space n) : ‖reverseData u‖ = ‖u‖ := by
  have hs : ‖reverseData u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_eq (reverseData u), norm_sq_eq u, value_reverseData_norm,
      velocity_reverseData_norm]
  nlinarith [norm_nonneg (reverseData u), norm_nonneg u]

theorem reverseData_involutive {n : ℕ} (u : Space n) : reverseData (reverseData u) = u := by
  apply h1_value_injective
  rw [value_reverseData]
  change reflectLpL (Ambient n) (value (reverseData u)) = value u
  rw [value_reverseData]
  exact reflectLpL_involutive _

theorem reverseData_add {n : ℕ} (u v : Space n) :
    reverseData (u + v) = reverseData u + reverseData v := by
  apply h1_value_injective
  have hs : value (u + v) = value u + value v := (valueL n).map_add u v
  have ht : value (reverseData u + reverseData v) =
      value (reverseData u) + value (reverseData v) := (valueL n).map_add _ _
  rw [value_reverseData]
  change reflectLpL (Ambient n) (value (u + v)) = _
  rw [hs, ht, value_reverseData, value_reverseData]
  exact (reflectLpL (Ambient n)).map_add _ _

theorem reverseData_smul {n : ℕ} (a : ℝ) (u : Space n) :
    reverseData (a • u) = a • reverseData u := by
  apply h1_value_injective
  have hs : value (a • u) = a • value u := (valueL n).map_smul a u
  have ht : value (a • reverseData u) = a • value (reverseData u) := (valueL n).map_smul _ _
  rw [value_reverseData]
  change reflectLpL (Ambient n) (value (a • u)) = _
  rw [hs, ht, value_reverseData]
  exact (reflectLpL (Ambient n)).map_smul _ _

def reverseDataLIE (n : ℕ) : Space n ≃ₗᵢ[ℝ] Space n where
  toFun := reverseData
  invFun := reverseData
  left_inv := reverseData_involutive
  right_inv := reverseData_involutive
  map_add' := reverseData_add
  map_smul' := reverseData_smul
  norm_map' := reverseData_norm

theorem reverseDataLIE_apply {n : ℕ} (u : Space n) : reverseDataLIE n u = reverseData u := rfl

theorem reverseData_isometry (n : ℕ) : Isometry (reverseData (n := n)) :=
  (reverseDataLIE n).isometry

theorem reverseData_mem_periodic_iff {n : ℕ} (u : Space n) :
    reverseData u ∈ periodicSubmodule n ↔ u ∈ periodicSubmodule n := by
  rw [mem_periodicSubmodule_iff, mem_periodicSubmodule_iff]
  change continuousRepresentative (reverseData u) 1 =
    continuousRepresentative (reverseData u) 0 ↔
      continuousRepresentative u 1 = continuousRepresentative u 0
  rw [representative_reverseData u (by norm_num), representative_reverseData u (by norm_num)]
  change continuousRepresentative u (1 - 1) = continuousRepresentative u (1 - 0) ↔ _
  simp only [sub_self, sub_zero]
  exact eq_comm

def reflectionInterval (t : ClosedInterval) : ClosedInterval :=
  ⟨reflection t, reflection_mem_Icc t.property⟩

theorem reflectionInterval_involutive : Function.Involutive reflectionInterval := by
  intro t
  apply Subtype.ext
  exact reflection_involutive t

def reverseSphere {n : ℕ} (u : SphereLoop n) : SphereLoop n where
  data := ⟨reverseData (u.data : Space n),
    (reverseData_mem_periodic_iff _).mpr u.data.property⟩
  sphere_constraint t := by
    rw [representative_reverseData _ t.property]
    exact u.sphere_constraint (reflectionInterval t)

theorem reverseSphere_data {n : ℕ} (u : SphereLoop n) :
    ((reverseSphere u).data : Space n) = reverseData (u.data : Space n) := rfl

theorem sphereRepresentative_reverseSphere {n : ℕ} (u : SphereLoop n) (t : ClosedInterval) :
    sphereRepresentative (reverseSphere u) t = sphereRepresentative u (reflectionInterval t) := by
  apply Subtype.ext
  exact representative_reverseData (u.data : Space n) t.property

theorem reverseSphere_involutive {n : ℕ} (u : SphereLoop n) :
    reverseSphere (reverseSphere u) = u := by
  apply sphereLoop_data_injective
  exact reverseData_involutive (u.data : Space n)

theorem reverseSphere_isometry (n : ℕ) : Isometry (reverseSphere (n := n)) := by
  intro u v
  calc
    edist (reverseSphere u) (reverseSphere v) =
        edist ((reverseSphere u).data : Space n) ((reverseSphere v).data : Space n) :=
      (sphereLoop_data_isometry n).edist_eq _ _
    _ = edist (u.data : Space n) (v.data : Space n) := (reverseData_isometry n) _ _
    _ = edist u v := ((sphereLoop_data_isometry n).edist_eq _ _).symm

theorem reverseSphere_continuous (n : ℕ) : Continuous (reverseSphere (n := n)) :=
  (reverseSphere_isometry n).continuous

theorem reverseSphere_constant {n : ℕ} (x : Sphere n) :
    reverseSphere (constantSphereLoop x) = constantSphereLoop x := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_reverseSphere, sphereRepresentative_constantSphereLoop,
    sphereRepresentative_constantSphereLoop]

theorem reverseSphere_ofSmooth {n : ℕ} (γ : Finsler.Loops.SmoothLoop n) :
    reverseSphere (Finsler.SmoothSobolev.ofSmooth γ) =
      Finsler.SmoothSobolev.ofSmooth (Finsler.Loops.reverse γ) := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_reverseSphere, Finsler.SmoothSobolev.sphereRepresentative_ofSmooth,
    Finsler.SmoothSobolev.sphereRepresentative_ofSmooth]
  change γ (1 - (t : ℝ)) = γ (-(t : ℝ))
  have h := γ.periodic (-(t : ℝ))
  convert h using 1
  congr 1
  ring

def sphereImage {n : ℕ} (u : SphereLoop n) : Set (Sphere n) := Set.range (sphereRepresentative u)

theorem sphereImage_ofSmooth {n : ℕ} (γ : Finsler.Loops.SmoothLoop n) :
    sphereImage (Finsler.SmoothSobolev.ofSmooth γ) = Finsler.Loops.image γ := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(t : ℝ), (Finsler.SmoothSobolev.sphereRepresentative_ofSmooth γ t).symm.trans ht⟩
  · rintro ⟨t, ht⟩
    let r : ClosedInterval := ⟨Int.fract t, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    refine ⟨r, ?_⟩
    rw [Finsler.SmoothSobolev.sphereRepresentative_ofSmooth]
    change γ (Int.fract t) = x
    rw [Finsler.SmoothSobolev.loop_eq_fract]
    exact ht

theorem sphereImage_reverseSphere {n : ℕ} (u : SphereLoop n) :
    sphereImage (reverseSphere u) = sphereImage u := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨reflectionInterval t, (sphereRepresentative_reverseSphere u t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨reflectionInterval t, ?_⟩
    rw [sphereRepresentative_reverseSphere, reflectionInterval_involutive]

theorem weakJet_reverseSphere_ae {n : ℕ} (u : SphereLoop n) :
    weakJet (reverseSphere u) =ᵐ[intervalMeasure]
      fun t => ((weakJet u (reflection t)).1, -(weakJet u (reflection t)).2) := by
  filter_upwards [velocity_reverseData_ae (u.data : Space n),
    ae_restrict_mem measurableSet_Ioo] with t hv ht
  apply Prod.ext
  · exact representative_reverseData (u.data : Space n) (Ioo_subset_Icc_self ht)
  · exact hv

theorem density_reverseSphere_ae {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    (fun t => Finsler.AmbientLagrangian.lagrangian F (weakJet (reverseSphere u) t))
      =ᵐ[intervalMeasure] fun t =>
        Finsler.AmbientLagrangian.lagrangian F (weakJet u (reflection t)) := by
  filter_upwards [weakJet_reverseSphere_ae u] with t ht
  rw [ht]
  have h := Finsler.EnergyConservation.lagrangian_velocity_smul F
    (weakJet u (reflection t)).1 (weakJet u (reflection t)).2 (-1)
  simpa only [neg_one_smul, neg_one_sq, one_mul] using h

theorem energy_reverseSphere {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    Finsler.SobolevEnergy.energy F (reverseSphere u) = Finsler.SobolevEnergy.energy F u := by
  change (∫ t, Finsler.AmbientLagrangian.lagrangian F (weakJet (reverseSphere u) t)
    ∂intervalMeasure) = _
  rw [integral_congr_ae (density_reverseSphere_ae F u)]
  exact reflection_measurePreserving.integral_comp (measurableEmbedding_subLeft (1 : ℝ))
    (fun t : ℝ => Finsler.AmbientLagrangian.lagrangian F (weakJet u t))

end

end Finsler.SobolevReverse
