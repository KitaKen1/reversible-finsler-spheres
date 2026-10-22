module

public import Finsler.Analysis.IntervalH1Energy
public import Finsler.Analysis.IntervalH1EnergyZero
public import Finsler.Geometry.EnergyConservation
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual smooth periodic sphere loops as elements of the actual weak H¹ graph.
The classical ambient derivative supplies the genuine weak derivative. The
continuous representative and weak jet agree with the original smooth loop,
so the actual Sobolev energy is the original smooth-loop energy. This does
not yet construct circle actions on arbitrary H¹ loops or H¹ first variation. -/

@[expose] public section

namespace Finsler.SmoothSobolev

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.Loops
open Finsler.Geometry Finsler.SphereRetraction Finsler.AmbientLagrangian
open MeasureTheory Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

theorem continuous_memLp_interval {H : Type*} [NormedAddCommGroup H]
    {f : ℝ → H} (hf : Continuous f) : MemLp f 2 intervalMeasure := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (0 : ℝ) 1))
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC t (Ioo_subset_Icc_self ht)

theorem position_memLp {n : ℕ} (γ : SmoothLoop n) :
    MemLp (Finsler.EnergyConservation.position γ) 2 intervalMeasure :=
  continuous_memLp_interval (Finsler.EnergyConservation.position_smooth γ).continuous

theorem position_fderiv_memLp {n : ℕ} (γ : SmoothLoop n) :
    MemLp (fderiv ℝ (Finsler.EnergyConservation.position γ)) 2 intervalMeasure :=
  continuous_memLp_interval
    ((Finsler.EnergyConservation.position_smooth γ).continuous_fderiv (by simp))

def smoothValueLp {n : ℕ} (γ : SmoothLoop n) : ValueLp n :=
  (position_memLp γ).toLp (Finsler.EnergyConservation.position γ)

def smoothDerivativeLp {n : ℕ} (γ : SmoothLoop n) : DerivativeLp n :=
  (position_fderiv_memLp γ).toLp (fderiv ℝ (Finsler.EnergyConservation.position γ))

theorem smoothValueLp_ae {n : ℕ} (γ : SmoothLoop n) :
    smoothValueLp γ =ᵐ[intervalMeasure] Finsler.EnergyConservation.position γ :=
  MemLp.coeFn_toLp (position_memLp γ)

theorem smoothDerivativeLp_ae {n : ℕ} (γ : SmoothLoop n) :
    smoothDerivativeLp γ =ᵐ[intervalMeasure]
      fderiv ℝ (Finsler.EnergyConservation.position γ) :=
  MemLp.coeFn_toLp (position_fderiv_memLp γ)

theorem smoothValue_hasWeakFDeriv {n : ℕ} (γ : SmoothLoop n) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (smoothValueLp γ))
      (smoothDerivativeLp γ) := by
  have hs := Finsler.EnergyConservation.position_smooth γ
  have hw := TauCeti.hasWeakFDerivOn_of_differentiableOn (μ := volume)
    (Ω := Finsler.IntervalSobolev.unitInterval)
    (hs.continuous.locallyIntegrable.locallyIntegrableOn (Finsler.IntervalSobolev.unitInterval : Set ℝ))
    ((hs.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn
      (Finsler.IntervalSobolev.unitInterval : Set ℝ))
    (fun t _ => hs.differentiable (by simp) t)
  exact (hw.congr_ae (smoothValueLp_ae γ).symm).congr_ae_deriv
    (smoothDerivativeLp_ae γ).symm

def graphData {n : ℕ} (γ : SmoothLoop n) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (smoothValueLp γ) (smoothDerivativeLp γ)
    (smoothValue_hasWeakFDeriv γ)

theorem value_graphData {n : ℕ} (γ : SmoothLoop n) :
    value (graphData γ) = smoothValueLp γ := by
  change TauCeti.WeakDerivStep.prevL (base n) (graphData γ) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_graphData {n : ℕ} (γ : SmoothLoop n) :
    derivative (graphData γ) = smoothDerivativeLp γ := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (graphData γ) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem value_graphData_ae {n : ℕ} (γ : SmoothLoop n) :
    value (graphData γ) =ᵐ[intervalMeasure] Finsler.EnergyConservation.position γ := by
  rw [value_graphData]
  exact smoothValueLp_ae γ

theorem velocity_graphData_ae {n : ℕ} (γ : SmoothLoop n) :
    velocity (graphData γ) =ᵐ[intervalMeasure] Finsler.EnergyConservation.velocity γ := by
  have hD : derivative (graphData γ) =ᵐ[intervalMeasure]
      fderiv ℝ (Finsler.EnergyConservation.position γ) := by
    rw [derivative_graphData]
    exact smoothDerivativeLp_ae γ
  filter_upwards [velocity_apply_ae (graphData γ), hD] with t hv hd
  rw [hd, fderiv_apply_one_eq_deriv, ← Finsler.EnergyConservation.velocity_eq_deriv] at hv
  exact hv

theorem representative_graphData {n : ℕ} (γ : SmoothLoop n) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    continuousRepresentative (graphData γ) t = (γ t : Ambient n) := by
  exact continuous_representative_unique (continuousRepresentative_continuousOn _)
    (Finsler.EnergyConservation.position_smooth γ).continuous.continuousOn
    (value_ae_continuousRepresentative _) (value_graphData_ae γ) ht

def ofSmooth {n : ℕ} (γ : SmoothLoop n) : SphereLoop n where
  data := ⟨graphData γ, by
    rw [mem_periodicSubmodule_iff]
    change continuousRepresentative (graphData γ) 1 = continuousRepresentative (graphData γ) 0
    rw [representative_graphData γ (by norm_num), representative_graphData γ (by norm_num)]
    exact congrArg (fun x : Sphere n => (x : Ambient n)) (by simpa using γ.periodic 0)⟩
  sphere_constraint t := by
    rw [representative_graphData γ t.property]
    simp

theorem sphereRepresentative_ofSmooth {n : ℕ} (γ : SmoothLoop n) (t : ClosedInterval) :
    sphereRepresentative (ofSmooth γ) t = γ t := by
  apply Subtype.ext
  exact representative_graphData γ t.property

theorem ofSmooth_constant {n : ℕ} (x : Sphere n) :
    ofSmooth (constant x) = constantSphereLoop x := by
  apply Finsler.SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_ofSmooth, sphereRepresentative_constantSphereLoop]
  rfl

theorem loop_eq_fract {n : ℕ} (γ : SmoothLoop n) (t : ℝ) : γ (Int.fract t) = γ t := by
  simpa only [Int.fract, mul_one] using γ.periodic.sub_int_mul_eq (x := t) ⌊t⌋

theorem ofSmooth_injective {n : ℕ} : Function.Injective (ofSmooth (n := n)) := by
  intro γ δ h
  apply loop_ext
  intro t
  let r : ClosedInterval := ⟨Int.fract t, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hr := congrArg (fun u : SphereLoop n => sphereRepresentative u r) h
  rw [sphereRepresentative_ofSmooth, sphereRepresentative_ofSmooth] at hr
  change γ (Int.fract t) = δ (Int.fract t) at hr
  rwa [loop_eq_fract, loop_eq_fract] at hr

/-- The smooth loops carry their actual induced H¹ metric here. -/
instance (n : ℕ) : MetricSpace (SmoothLoop n) :=
  MetricSpace.induced (ofSmooth (n := n)) ofSmooth_injective inferInstance

theorem ofSmooth_isometry (n : ℕ) : Isometry (ofSmooth (n := n)) := fun _ _ => rfl

theorem ofSmooth_tendsto_iff {n : ℕ} {I : Type*} {l : Filter I}
    {v : I → SmoothLoop n} {γ : SmoothLoop n} :
    Tendsto (fun i => ofSmooth (v i)) l (𝓝 (ofSmooth γ)) ↔ Tendsto v l (𝓝 γ) :=
  (ofSmooth_isometry n).isEmbedding.tendsto_nhds_iff.symm

theorem weakJet_ofSmooth_ae {n : ℕ} (γ : SmoothLoop n) :
    weakJet (ofSmooth γ) =ᵐ[intervalMeasure] loopJet γ := by
  filter_upwards [velocity_graphData_ae γ, ae_restrict_mem measurableSet_Ioo] with t hv ht
  rw [Finsler.EnergyConservation.loopJet_eq]
  apply Prod.ext
  · exact representative_graphData γ (Ioo_subset_Icc_self ht)
  · exact hv

theorem density_ofSmooth_ae {n : ℕ} (F : ReversibleMetric n) (γ : SmoothLoop n) :
    (fun t => lagrangian F (weakJet (ofSmooth γ) t)) =ᵐ[intervalMeasure]
      Finsler.LoopEnergy.density F γ := by
  filter_upwards [weakJet_ofSmooth_ae γ] with t ht
  rw [ht]
  exact lagrangian_ambientPair F _

theorem energy_ofSmooth {n : ℕ} (F : ReversibleMetric n) (γ : SmoothLoop n) :
    Finsler.SobolevEnergy.energy F (ofSmooth γ) = Finsler.LoopEnergy.energy F γ := by
  change (∫ t, lagrangian F (weakJet (ofSmooth γ) t) ∂intervalMeasure) = _
  rw [integral_congr_ae (density_ofSmooth_ae F γ)]
  change (∫ t in Ioo (0 : ℝ) 1, Finsler.LoopEnergy.density F γ t) = _
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

theorem energy_ofSmooth_shift {n : ℕ} (F : ReversibleMetric n) (γ : SmoothLoop n) (a : ℝ) :
    Finsler.SobolevEnergy.energy F (ofSmooth (shift γ a)) =
      Finsler.SobolevEnergy.energy F (ofSmooth γ) := by
  rw [energy_ofSmooth, energy_ofSmooth]
  exact Finsler.LoopEnergy.energy_shift F γ a

theorem energy_ofSmooth_reverse {n : ℕ} (F : ReversibleMetric n) (γ : SmoothLoop n) :
    Finsler.SobolevEnergy.energy F (ofSmooth (reverse γ)) =
      Finsler.SobolevEnergy.energy F (ofSmooth γ) := by
  rw [energy_ofSmooth, energy_ofSmooth]
  exact Finsler.LoopEnergy.energy_reverse F γ

theorem energy_ofSmooth_iterate {n : ℕ} (F : ReversibleMetric n) (γ : SmoothLoop n) (k : ℕ) :
    Finsler.SobolevEnergy.energy F (ofSmooth (iterate γ k)) =
      (k : ℝ) ^ 2 * Finsler.SobolevEnergy.energy F (ofSmooth γ) := by
  rw [energy_ofSmooth, energy_ofSmooth]
  exact Finsler.LoopEnergy.energy_iterate F γ k

theorem energy_ofSmooth_variation {n : ℕ} (F : ReversibleMetric n)
    (V : Finsler.Geodesics.SmoothVariation n) :
    (fun s => Finsler.SobolevEnergy.energy F (ofSmooth (Finsler.Geodesics.loopAt V s))) =
      (fun s => Finsler.LoopEnergy.energy F (Finsler.Geodesics.loopAt V s)) :=
  funext fun s => energy_ofSmooth F (Finsler.Geodesics.loopAt V s)

theorem smoothVariation_energy_hasDerivAt {n : ℕ} (F : ReversibleMetric n)
    (V : Finsler.Geodesics.SmoothVariation n) {s : ℝ}
    (hreg : Finsler.Geodesics.Regular (Finsler.Geodesics.loopAt V s)) :
    HasDerivAt (fun r => Finsler.SobolevEnergy.energy F
      (ofSmooth (Finsler.Geodesics.loopAt V r))) (Finsler.FirstVariation.firstVariation F V s) s := by
  rw [energy_ofSmooth_variation]
  exact Finsler.FirstVariation.energy_hasDerivAt F V hreg

theorem stationary_iff_smoothSobolev_variations {n : ℕ} (F : ReversibleMetric n)
    (γ : SmoothLoop n) : Finsler.Geodesics.Stationary F γ ↔
      ∀ V : Finsler.Geodesics.SmoothVariation n, Finsler.Geodesics.loopAt V 0 = γ →
        HasDerivAt (fun s => Finsler.SobolevEnergy.energy F
          (ofSmooth (Finsler.Geodesics.loopAt V s))) 0 0 := by
  change (∀ V : Finsler.Geodesics.SmoothVariation n, Finsler.Geodesics.loopAt V 0 = γ →
    HasDerivAt (fun s => Finsler.LoopEnergy.energy F (Finsler.Geodesics.loopAt V s)) 0 0) ↔ _
  simp only [energy_ofSmooth_variation]

theorem nonconstant_iff_no_constant {n : ℕ} (γ : SmoothLoop n) :
    Nonconstant γ ↔ ¬ ∃ x : Sphere n, γ = constant x := by
  constructor
  · rintro ⟨s, t, h⟩ ⟨x, rfl⟩
    exact h rfl
  · intro hn
    by_contra hc
    apply hn
    refine ⟨γ 0, loop_ext fun t => ?_⟩
    by_contra ht
    exact hc ⟨t, 0, ht⟩

theorem ofSmooth_nonconstant_iff {n : ℕ} (γ : SmoothLoop n) :
    (¬ ∃ x : Sphere n, ofSmooth γ = constantSphereLoop x) ↔ Nonconstant γ := by
  rw [nonconstant_iff_no_constant]
  have h : (∃ x : Sphere n, ofSmooth γ = constantSphereLoop x) ↔
      ∃ x : Sphere n, γ = constant x := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, ofSmooth_injective (hx.trans (ofSmooth_constant x).symm)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, ofSmooth_constant x⟩
  exact not_congr h

theorem energy_ofSmooth_pos_iff {n : ℕ} (F : ReversibleMetric n) (γ : SmoothLoop n) :
    0 < Finsler.SobolevEnergy.energy F (ofSmooth γ) ↔ Nonconstant γ := by
  rw [Finsler.SobolevEnergy.energy_pos_iff_nonconstant, ofSmooth_nonconstant_iff]

end

end Finsler.SmoothSobolev
