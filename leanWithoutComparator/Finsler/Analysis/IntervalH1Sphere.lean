module

public import Finsler.Analysis.IntervalH1Trace
public import Finsler.Geometry.MetricComparison

/-! Periodic sphere-valued interval H¹ data with their actual weak tangent jet.
The data are the closed weak-derivative graph, with equal endpoint traces and
the genuine unit-sphere constraint. Circle actions, smooth-loop embedding and
energy differentiability remain separate work. -/

@[expose] public section

namespace Finsler.IntervalSobolev

open Finsler.SphereGeometry MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

theorem continuousRepresentative_hasDerivAt_ae {n : ℕ} (u : Space n) :
    ∀ᵐ t ∂intervalMeasure, HasDerivAt (continuousRepresentative u) (velocity u t) t := by
  obtain ⟨c, hc⟩ := (exists_continuous_representative u).choose_spec.2.2
  change ∀ t, continuousRepresentative u t =
    c + Finsler.IntervalPrimitive.primitive (velocity u) t at hc
  change ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), _
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [(velocity_intervalIntegrable u).ae_hasDerivAt_integral] with t hd ht
  have htu : t ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using Ioo_subset_Icc_self ht
  have hp := hd htu 0 (show (0 : ℝ) ∈ uIcc 0 1 by norm_num)
  have hq := (hasDerivAt_const t c).add hp
  rw [show continuousRepresentative u =
    (fun s => c + Finsler.IntervalPrimitive.primitive (velocity u) s) from funext hc]
  change HasDerivAt (fun s => c + ∫ x in (0 : ℝ)..s, velocity u x) (velocity u t) t
  change HasDerivAt (fun s => c + ∫ x in (0 : ℝ)..s, velocity u x) (0 + velocity u t) t at hq
  simpa only [zero_add] using hq

structure SphereLoop (n : ℕ) where
  data : periodicSubmodule n
  sphere_constraint : ∀ t : ClosedInterval, ‖continuousRepresentative (data : Space n) t‖ = 1

theorem sphereLoop_data_injective {n : ℕ} :
    Function.Injective (fun u : SphereLoop n => (u.data : Space n)) := by
  intro u v h
  have hd : u.data = v.data := Subtype.ext h
  cases u
  cases v
  cases hd
  rfl

instance (n : ℕ) : MetricSpace (SphereLoop n) :=
  MetricSpace.induced (fun u => (u.data : Space n)) sphereLoop_data_injective inferInstance

theorem sphereLoop_data_isometry (n : ℕ) :
    Isometry (fun u : SphereLoop n => (u.data : Space n)) := fun _ _ => rfl

theorem sphereLoop_tendsto_iff {n : ℕ} {I : Type*} {l : Filter I}
    {v : I → SphereLoop n} {u : SphereLoop n} :
    Tendsto v l (𝓝 u) ↔ Tendsto (fun i => (v i).data : I → Space n) l (𝓝 (u.data : Space n)) :=
  (sphereLoop_data_isometry n).isEmbedding.tendsto_nhds_iff

def sphereDataSet (n : ℕ) : Set (Space n) :=
  {u | u ∈ periodicSubmodule n ∧ ∀ t : ClosedInterval, ‖traceL n t u‖ = 1}

theorem sphereLoop_data_range (n : ℕ) :
    Set.range (fun u : SphereLoop n => (u.data : Space n)) = sphereDataSet n := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.data.property, v.sphere_constraint⟩
  · rintro ⟨hp, hs⟩
    exact ⟨⟨⟨u, hp⟩, hs⟩, rfl⟩

theorem sphereDataSet_closed (n : ℕ) : IsClosed (sphereDataSet n) := by
  have hc : IsClosed {u : Space n | ∀ t : ClosedInterval, ‖traceL n t u‖ = 1} := by
    have h := isClosed_iInter fun t : ClosedInterval =>
      isClosed_eq (traceL n t).continuous.norm (continuous_const : Continuous fun _ : Space n => (1 : ℝ))
    simpa only [Set.iInter_ofPred] using h
  exact (periodicSubmodule_closed n).inter hc

instance (n : ℕ) : CompleteSpace (SphereLoop n) :=
  (sphereLoop_data_isometry n).isUniformInducing.completeSpace (by
    rw [sphereLoop_data_range]
    exact (sphereDataSet_closed n).isComplete)

theorem sphereLoop_complete (n : ℕ) : IsComplete (Set.univ : Set (SphereLoop n)) :=
  isComplete_univ

def constantValue {n : ℕ} (x : Ambient n) : ValueLp n := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  exact (memLp_const x).toLp (fun _ : ℝ => x)

theorem constantValue_ae {n : ℕ} (x : Ambient n) :
    constantValue x =ᵐ[intervalMeasure] fun _ => x := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  exact MemLp.coeFn_toLp (memLp_const x)

theorem constantValue_hasWeakFDeriv {n : ℕ} (x : Ambient n) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (constantValue x))
      (0 : DerivativeLp n) := by
  have h : TauCeti.HasWeakFDerivOn volume unitInterval (fun _ : ℝ => x)
      (fun _ : ℝ => (0 : ℝ →L[ℝ] Ambient n)) := by
    apply TauCeti.hasWeakFDerivOn_iff.mpr
    intro v
    exact TauCeti.hasWeakLineDerivOn_const x
  have hzero : (fun _ : ℝ => (0 : ℝ →L[ℝ] Ambient n)) =ᵐ[intervalMeasure]
      (0 : DerivativeLp n) := (Lp.coeFn_zero _ _ _).symm
  exact (h.congr_ae (constantValue_ae x).symm).congr_ae_deriv hzero

def constantData {n : ℕ} (x : Ambient n) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (constantValue x) 0 (constantValue_hasWeakFDeriv x)

theorem value_constantData {n : ℕ} (x : Ambient n) :
    value (constantData x) = constantValue x := by
  change TauCeti.WeakDerivStep.prevL (base n) (constantData x) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_constantData {n : ℕ} (x : Ambient n) :
    derivative (constantData x) = 0 := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (constantData x) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem velocity_constantData {n : ℕ} (x : Ambient n) : velocity (constantData x) = 0 := by
  apply norm_eq_zero.mp
  rw [velocity_norm_eq, derivative_constantData, norm_zero]

theorem continuousRepresentative_constantData {n : ℕ} (x : Ambient n) {t : ℝ}
    (ht : t ∈ Icc 0 1) : continuousRepresentative (constantData x) t = x := by
  apply continuous_representative_unique (continuousRepresentative_continuousOn _)
    continuousOn_const (value_ae_continuousRepresentative _) _ ht
  rw [value_constantData]
  exact constantValue_ae x

def constantSphereLoop {n : ℕ} (x : Sphere n) : SphereLoop n where
  data := ⟨constantData x, by
    rw [mem_periodicSubmodule_iff]
    change continuousRepresentative (constantData (x : Ambient n)) 1 =
      continuousRepresentative (constantData (x : Ambient n)) 0
    rw [continuousRepresentative_constantData _ (by norm_num),
      continuousRepresentative_constantData _ (by norm_num)]⟩
  sphere_constraint t := by
    rw [continuousRepresentative_constantData _ t.property]
    simp

theorem sphereLoop_nonempty (n : ℕ) : Nonempty (SphereLoop n) := by
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := Ambient n)
    (x := (0 : Ambient n))).mpr zero_le_one
  exact ⟨constantSphereLoop ⟨x, hx⟩⟩

def sphereRepresentative {n : ℕ} (u : SphereLoop n) (t : ClosedInterval) : Sphere n :=
  ⟨continuousRepresentative (u.data : Space n) t, by simpa using u.sphere_constraint t⟩

theorem sphereRepresentative_constantSphereLoop {n : ℕ} (x : Sphere n) (t : ClosedInterval) :
    sphereRepresentative (constantSphereLoop x) t = x := by
  apply Subtype.ext
  exact continuousRepresentative_constantData (x : Ambient n) t.property

theorem sphereRepresentative_continuous {n : ℕ} (u : SphereLoop n) :
    Continuous (sphereRepresentative u) := by
  exact ((representativeL n (u.data : Space n)).continuous).subtype_mk _

theorem sphereRepresentative_endpoints {n : ℕ} (u : SphereLoop n) :
    sphereRepresentative u ⟨1, by norm_num⟩ = sphereRepresentative u ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  exact (mem_periodicSubmodule_iff (u.data : Space n)).mp u.data.property

theorem weakVelocity_orthogonal_ae {n : ℕ} (u : SphereLoop n) :
    ∀ᵐ t ∂intervalMeasure,
      ⟪continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t⟫ = 0 := by
  have hmem : ∀ᵐ t ∂intervalMeasure, t ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [continuousRepresentative_hasDerivAt_ae (u.data : Space n), hmem] with t hd ht
  have heq : (fun s => ‖continuousRepresentative (u.data : Space n) s‖ ^ 2) =ᶠ[𝓝 t]
      fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [u.sphere_constraint ⟨s, Ioo_subset_Icc_self hs⟩]
    norm_num
  have hz : deriv (fun s => ‖continuousRepresentative (u.data : Space n) s‖ ^ 2) t = 0 :=
    heq.deriv_eq.trans (deriv_const t 1)
  have h := hd.norm_sq.deriv
  rw [hz] at h
  linarith

def weakJet {n : ℕ} (u : SphereLoop n) (t : ℝ) : Ambient n × Ambient n :=
  (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)

theorem weakJet_aestronglyMeasurable {n : ℕ} (u : SphereLoop n) :
    AEStronglyMeasurable (weakJet u) intervalMeasure := by
  have hq := (Lp.aestronglyMeasurable (value (u.data : Space n))).congr
    (value_ae_continuousRepresentative (u.data : Space n))
  exact hq.prodMk (Lp.aestronglyMeasurable (velocity (u.data : Space n)))

theorem weakJet_has_tangent_ae {n : ℕ} (u : SphereLoop n) :
    ∀ᵐ t ∂intervalMeasure, ∃ p : Total n, Finsler.SphereRetraction.ambientPair p = weakJet u t := by
  have hmem : ∀ᵐ t ∂intervalMeasure, t ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [weakVelocity_orthogonal_ae u, hmem] with t ho ht
  let x : Sphere n := sphereRepresentative u ⟨t, Ioo_subset_Icc_self ht⟩
  have hr : velocity (u.data : Space n) t ∈ (ambientMap x).range := by
    rw [ambientMap_range]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ho
  obtain ⟨w, hw⟩ := hr
  refine ⟨⟨x, w⟩, ?_⟩
  exact Prod.ext rfl hw

end

end Finsler.IntervalSobolev
