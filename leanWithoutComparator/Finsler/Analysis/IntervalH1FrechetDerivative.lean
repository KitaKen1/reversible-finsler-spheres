module

public import Finsler.Analysis.IntervalH1DirectionalDerivative
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Frechet differentiation of the actual ambient integral energy in the
original weak H1 norm. A scalar mean value estimate turns the previously
proved directional derivatives and operator norm continuity into a uniform
little-o remainder. Intrinsic sphere charts and critical regularity are separate. -/

@[expose] public section

namespace Finsler.AmbientSobolevEnergy

open Finsler.Geometry Finsler.IntervalSobolev Set Filter
open scoped Topology

noncomputable section

section MeanValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {A : E → E →L[ℝ] ℝ} {s : Set E}

theorem line_hasDerivAt_of_local_directions
    (hd : ∀ z ∈ s, ∀ h, HasDerivAt (fun r : ℝ => f (z + r • h)) (A z h) 0)
    (x h : E) (t : ℝ) (ht : x + t • h ∈ s) :
    HasDerivAt (fun r : ℝ => f (x + r • h)) (A (x + t • h) h) t := by
  have hh : HasDerivAt (fun r : ℝ => f ((x + t • h) + r • h))
      (A (x + t • h) h) (t - t) := by simpa using hd _ ht h
  have hh := hh.comp_sub_const t t
  have he : (fun r : ℝ => f ((x + t • h) + (r - t) • h)) =
      (fun r : ℝ => f (x + r • h)) := by
    funext r
    congr 1
    rw [sub_smul]
    abel
  rw [he] at hh
  exact hh

theorem remainder_bound_of_local_directions
    (hd : ∀ z ∈ s, ∀ h, HasDerivAt (fun r : ℝ => f (z + r • h)) (A z h) 0)
    (x y : E) (ε : ℝ)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ s)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + t • (y - x)) - A x‖ ≤ ε) :
    ‖f y - f x - A x (y - x)‖ ≤ ε * ‖y - x‖ := by
  let g : ℝ → ℝ := fun t => f (x + t • (y - x)) - t * A x (y - x)
  let g' : ℝ → ℝ := fun t => (A (x + t • (y - x)) - A x) (y - x)
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hh := (line_hasDerivAt_of_local_directions hd x (y - x) t (hs t ht)).fun_sub
      ((hasDerivAt_id t).mul_const (A x (y - x)))
    simpa only [g, g', id_eq, one_mul, Pi.sub_apply, sub_apply] using
      hh.hasDerivWithinAt
  have bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖g' t‖ ≤ ε * ‖y - x‖ := by
    intro t ht
    exact ContinuousLinearMap.le_of_opNorm_le _ (hb t (Ico_subset_Icc_self ht)) _
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01' hg bound
  simpa [g, sub_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh

theorem hasFDerivAt_of_continuous_local_directions
    (hs : IsOpen s)
    (hd : ∀ z ∈ s, ∀ h, HasDerivAt (fun r : ℝ => f (z + r • h)) (A z h) 0)
    {x : E} (hx : x ∈ s) (hA : ContinuousAt A x) : HasFDerivAt f (A x) x := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have he : ∀ᶠ z in 𝓝 x, ‖A z - A x‖ < ε := by
    have hh : ∀ᶠ z in 𝓝 x, A z ∈ Metric.ball (A x) ε :=
      hA (Metric.ball_mem_nhds (A x) hε)
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hh
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hs.mem_nhds hx) he)
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Metric.ball x δ := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm]
    have hn : ‖t • (y - x)‖ ≤ ‖y - x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    simpa only [add_sub_cancel_left] using hn.trans_lt (by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  exact remainder_bound_of_local_directions hd x y ε
    (fun t ht => (hb (hseg t ht)).1)
    (fun t ht => (hb (hseg t ht)).2.le)

end MeanValue

variable {n : ℕ}

def localVariationExtension (F : ReversibleMetric n) (u : SphereLoop n)
    (v : Space n) : Space n →L[ℝ] ℝ := by
  classical
  exact if hv : v ∈ neighbourhood u then variationL F ⟨v, hv⟩ else 0

theorem localVariationExtension_eq (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : localVariationExtension F u (v : Space n) = variationL F v := by
  simp only [localVariationExtension, dite_eq_left v.property]

theorem localVariationExtension_continuousOn (F : ReversibleMetric n) (u : SphereLoop n) :
    ContinuousOn (localVariationExtension F u) (neighbourhood u) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (neighbourhood u).domRestrict (localVariationExtension F u) =
      (fun v : LocalSpace u => variationL F v) := by
    funext v
    exact localVariationExtension_eq F v
  rw [he]
  exact variationL_continuous F u

theorem localVariationExtension_continuousAt (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : ContinuousAt (localVariationExtension F u) (v : Space n) :=
  (localVariationExtension_continuousOn F u).continuousAt
    ((neighbourhood_open u).mem_nhds v.property)

theorem ambientEnergy_hasFDerivAt (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : HasFDerivAt (ambientEnergy F) (variationL F v) (v : Space n) := by
  rw [← localVariationExtension_eq F v]
  apply hasFDerivAt_of_continuous_local_directions (neighbourhood_open u) _ v.property
    (localVariationExtension_continuousAt F v)
  intro z hz h
  simpa only [localVariationExtension, dite_eq_left hz] using
    ambientEnergy_hasDerivAt_zero F (⟨z, hz⟩ : LocalSpace u) h

theorem ambientEnergy_fderiv_eq (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : fderiv ℝ (ambientEnergy F) (v : Space n) = variationL F v :=
  (ambientEnergy_hasFDerivAt F v).fderiv

theorem ambientEnergy_remainder_isLittleO (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) :
    (fun y : Space n => ambientEnergy F y - ambientEnergy F (v : Space n) -
      variationL F v (y - (v : Space n))) =o[𝓝 (v : Space n)]
        (fun y : Space n => y - (v : Space n)) :=
  (ambientEnergy_hasFDerivAt F v).isLittleO

theorem ambientEnergy_differentiableOn (F : ReversibleMetric n) (u : SphereLoop n) :
    DifferentiableOn ℝ (ambientEnergy F) (neighbourhood u) := by
  intro v hv
  exact (ambientEnergy_hasFDerivAt F (⟨v, hv⟩ : LocalSpace u)).differentiableAt.differentiableWithinAt

theorem ambientEnergy_fderiv_continuousOn (F : ReversibleMetric n) (u : SphereLoop n) :
    ContinuousOn (fderiv ℝ (ambientEnergy F)) (neighbourhood u) := by
  apply (localVariationExtension_continuousOn F u).congr
  intro v hv
  rw [ambientEnergy_fderiv_eq F (⟨v, hv⟩ : LocalSpace u)]
  exact (localVariationExtension_eq F (⟨v, hv⟩ : LocalSpace u)).symm

theorem ambientEnergy_contDiffOn_one (F : ReversibleMetric n) (u : SphereLoop n) :
    ContDiffOn ℝ 1 (ambientEnergy F) (neighbourhood u) := by
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) (neighbourhood_open u)).mpr
  refine ⟨ambientEnergy_differentiableOn F u, ?_, ?_⟩
  · simp
  · exact contDiffOn_zero.mpr (ambientEnergy_fderiv_continuousOn F u)

theorem ambientEnergy_contDiffAt_one (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : ContDiffAt ℝ 1 (ambientEnergy F) (v : Space n) :=
  (ambientEnergy_contDiffOn_one F u).contDiffAt
    ((neighbourhood_open u).mem_nhds v.property)

theorem ambientEnergy_hasStrictFDerivAt (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) :
    HasStrictFDerivAt (ambientEnergy F) (variationL F v) (v : Space n) := by
  rw [← localVariationExtension_eq F v]
  apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt _
    (localVariationExtension_continuousAt F v)
  filter_upwards [(neighbourhood_open u).mem_nhds v.property] with z hz
  simpa only [localVariationExtension, dite_eq_left hz] using
    ambientEnergy_hasFDerivAt F (⟨z, hz⟩ : LocalSpace u)

theorem variationL_eq_of_same_basepoint (F : ReversibleMetric n)
    {u w : SphereLoop n} (v : LocalSpace u) (z : LocalSpace w)
    (he : (v : Space n) = (z : Space n)) : variationL F v = variationL F z := by
  have hh := ambientEnergy_hasFDerivAt F v
  rw [he] at hh
  exact hh.unique (ambientEnergy_hasFDerivAt F z)

theorem ambientEnergy_hasFDerivAt_sphere_centre (F : ReversibleMetric n) (u : SphereLoop n) :
    HasFDerivAt (ambientEnergy F) (Finsler.SobolevEnergyDifferential.variationL F u)
      (u.data : Space n) := by
  have hh := ambientEnergy_hasFDerivAt F (centre u)
  rw [variationL_centre] at hh
  simpa only [centre] using hh

end

end Finsler.AmbientSobolevEnergy
