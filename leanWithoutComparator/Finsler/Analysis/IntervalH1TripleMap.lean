module

public import Finsler.Analysis.IntervalH1RadialRetraction

/-! One-dimensional superposition for triples: a C¹ map of three original weak H¹ graph
elements is a graph element, with value the map of the continuous representatives and
weak velocity the derivative applied to the three weak velocities, certified by the
one-dimensional chain rule. -/

@[expose] public section

namespace Finsler.SobolevTripleMap

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevOfPrimitive
open Finsler.SobolevPairMap Finsler.IntervalChainRule
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

abbrev E3 (n : ℕ) := Ambient n × Ambient n × Ambient n

def tripleRep (u h b : Space n) (t : ℝ) : E3 n :=
  (continuousRepresentative u t, continuousRepresentative h t, continuousRepresentative b t)

def tripleVel (u h b : Space n) (t : ℝ) : E3 n := (velocity u t, velocity h t, velocity b t)

theorem tripleRep_continuousOn (u h b : Space n) : ContinuousOn (tripleRep u h b) (Icc 0 1) :=
  (continuousRepresentative_continuousOn u).prodMk
    ((continuousRepresentative_continuousOn h).prodMk (continuousRepresentative_continuousOn b))

theorem tripleVel_intervalIntegrable (u h b : Space n) :
    IntervalIntegrable (tripleVel u h b) volume 0 1 := by
  have hu := velocity_intervalIntegrable u
  have hh := velocity_intervalIntegrable h
  have hb := velocity_intervalIntegrable b
  exact ⟨hu.1.prodMk (hh.1.prodMk hb.1), hu.2.prodMk (hh.2.prodMk hb.2)⟩

theorem tripleRep_eq_add_integral (u h b : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tripleRep u h b t = tripleRep u h b 0 + ∫ s in (0 : ℝ)..t, tripleVel u h b s := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (tripleVel_intervalIntegrable u h b).mono_set hsub
  have h1 : (∫ s in (0 : ℝ)..t, tripleVel u h b s).1 = ∫ s in (0 : ℝ)..t, velocity u s := by
    have := (ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n × Ambient n)).intervalIntegral_comp_comm hint
    simpa [tripleVel] using this.symm
  have h23 : (∫ s in (0 : ℝ)..t, tripleVel u h b s).2 =
      ∫ s in (0 : ℝ)..t, (velocity h s, velocity b s) := by
    have := (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n)).intervalIntegral_comp_comm hint
    simpa [tripleVel] using this.symm
  have hint2 : IntervalIntegrable (fun s => (velocity h s, velocity b s)) volume 0 t := by
    have hh := velocity_intervalIntegrable h
    have hb := velocity_intervalIntegrable b
    have hfull : IntervalIntegrable (fun s => (velocity h s, velocity b s)) volume 0 1 :=
      ⟨hh.1.prodMk hb.1, hh.2.prodMk hb.2⟩
    exact hfull.mono_set hsub
  have h2 : (∫ s in (0 : ℝ)..t, (velocity h s, velocity b s)).1 = ∫ s in (0 : ℝ)..t, velocity h s := by
    have := (ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).intervalIntegral_comp_comm hint2
    simpa using this.symm
  have h3 : (∫ s in (0 : ℝ)..t, (velocity h s, velocity b s)).2 = ∫ s in (0 : ℝ)..t, velocity b s := by
    have := (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)).intervalIntegral_comp_comm hint2
    simpa using this.symm
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [Prod.fst_add, h1, ← continuousRepresentative_sub u h0 ht]
    simp only [tripleRep]
    abel
  · rw [Prod.snd_add, Prod.fst_add, h23, h2, ← continuousRepresentative_sub h h0 ht]
    simp only [tripleRep]
    abel
  · rw [Prod.snd_add, Prod.snd_add, h23, h3, ← continuousRepresentative_sub b h0 ht]
    simp only [tripleRep]
    abel

theorem tripleRep_hasDerivAt_ae (u h b : Space n) :
    ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), HasDerivAt (tripleRep u h b) (tripleVel u h b s) s := by
  have hu := continuousRepresentative_hasDerivAt_ae u
  have hh := continuousRepresentative_hasDerivAt_ae h
  have hb := continuousRepresentative_hasDerivAt_ae b
  change ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at hu hh hb
  filter_upwards [hu, hh, hb] with s h1 h2 h3
  exact h1.prodMk (h2.prodMk h3)

theorem velocityTriple_memLp (u h b : Space n) :
    MemLp (fun s => ‖velocity u s‖ + ‖velocity h s‖ + ‖velocity b s‖) 2 intervalMeasure :=
  ((Lp.memLp (velocity u)).norm.add (Lp.memLp (velocity h)).norm).add (Lp.memLp (velocity b)).norm

theorem norm_tripleVel_le (u h b : Space n) (s : ℝ) :
    ‖tripleVel u h b s‖ ≤ ‖velocity u s‖ + ‖velocity h s‖ + ‖velocity b s‖ := by
  have hu := norm_nonneg (velocity u s)
  have hh := norm_nonneg (velocity h s)
  have hb := norm_nonneg (velocity b s)
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · change ‖velocity u s‖ ≤ _
    linarith
  · change ‖velocity h s‖ ≤ _
    linarith
  · change ‖velocity b s‖ ≤ _
    linarith

variable {Γ : E3 n → Ambient n}

theorem mapValue_continuousOn (hΓ : ContDiff ℝ 1 Γ) (u h b : Space n) :
    ContinuousOn (fun t => Γ (tripleRep u h b t)) (Icc 0 1) :=
  hΓ.continuous.comp_continuousOn (tripleRep_continuousOn u h b)

theorem mapVelocity_memLp (hΓ : ContDiff ℝ 1 Γ) (u h b : Space n) :
    MemLp (fun t => fderiv ℝ Γ (tripleRep u h b t) (tripleVel u h b t)) 2 intervalMeasure := by
  have hD : ContinuousOn (fun s => fderiv ℝ Γ (tripleRep u h b s)) (Icc 0 1) :=
    (hΓ.continuous_fderiv (by norm_num)).comp_continuousOn (tripleRep_continuousOn u h b)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hmeas : AEStronglyMeasurable (fun t => fderiv ℝ Γ (tripleRep u h b t) (tripleVel u h b t))
      intervalMeasure := by
    have he : Continuous (fun p : (E3 n →L[ℝ] Ambient n) × E3 n => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have hD' : AEStronglyMeasurable (fun s => fderiv ℝ Γ (tripleRep u h b s)) intervalMeasure :=
      (hD.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
    have hV : AEStronglyMeasurable (tripleVel u h b) intervalMeasure :=
      (Lp.aestronglyMeasurable (velocity u)).prodMk
        ((Lp.aestronglyMeasurable (velocity h)).prodMk (Lp.aestronglyMeasurable (velocity b)))
    exact he.comp_aestronglyMeasurable (hD'.prodMk hV)
  refine (velocityTriple_memLp u h b).of_le_mul (c := C) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have h2 := hC s (Ioo_subset_Icc_self hs)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    ‖fderiv ℝ Γ (tripleRep u h b s) (tripleVel u h b s)‖ ≤
        ‖fderiv ℝ Γ (tripleRep u h b s)‖ * ‖tripleVel u h b s‖ := (fderiv ℝ Γ _).le_opNorm _
    _ ≤ C * (‖velocity u s‖ + ‖velocity h s‖ + ‖velocity b s‖) :=
      mul_le_mul h2 (norm_tripleVel_le u h b s) (norm_nonneg _) ((norm_nonneg _).trans h2)

theorem mapValue_prim (hΓ : ContDiff ℝ 1 Γ) (u h b : Space n) :
    ∀ t ∈ Icc (0 : ℝ) 1, Γ (tripleRep u h b t) =
      Γ (tripleRep u h b 0) + ∫ s in (0 : ℝ)..t, fderiv ℝ Γ (tripleRep u h b s) (tripleVel u h b s) := by
  intro t ht
  have hc := comp_sub_eq_integral hΓ (tripleVel_intervalIntegrable u h b)
    (fun t ht => tripleRep_eq_add_integral u h b ht) (tripleRep_hasDerivAt_ae u h b) ht
  rw [← hc]
  abel

/-- A C¹ map of a triple of graph elements, as a graph element. -/
def tripleData (hΓ : ContDiff ℝ 1 Γ) (u h b : Space n) : Space n :=
  ofPrimitive (mapValue_continuousOn hΓ u h b) (mapVelocity_memLp hΓ u h b) (mapValue_prim hΓ u h b)

theorem value_tripleData_ae (hΓ : ContDiff ℝ 1 Γ) (u h b : Space n) :
    value (tripleData hΓ u h b) =ᵐ[intervalMeasure] fun t => Γ (tripleRep u h b t) :=
  value_ofPrimitive_ae _ _ _

theorem velocity_tripleData_ae (hΓ : ContDiff ℝ 1 Γ) (u h b : Space n) :
    velocity (tripleData hΓ u h b) =ᵐ[intervalMeasure]
      fun t => fderiv ℝ Γ (tripleRep u h b t) (tripleVel u h b t) :=
  velocity_ofPrimitive_ae _ _ _

theorem representative_tripleData (hΓ : ContDiff ℝ 1 Γ) (u h b : Space n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (tripleData hΓ u h b) t = Γ (tripleRep u h b t) :=
  representative_ofPrimitive _ _ _ ht

end

end Finsler.SobolevTripleMap
