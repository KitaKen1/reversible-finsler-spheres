module

public import Finsler.Geometry.PolygonSmooth

/-! Global properties of the polygon energy on sphere polygons. The Finsler distance is
Lipschitz with respect to the ambient distance for nearby points of the sphere, by the triangle
inequality and the round upper bound; so the distance, the minimal energy and the polygon energy
are continuous on all sphere polygons. A polygon of energy at most b has all edges of squared
length at most b / (c N), where c is the round lower constant; so for N large the polygons of
bounded energy are short. Normalization is invariant under positive rescaling, hence so is the
polygon energy with normalized vertices in every vertex. If the polygon energy with normalized
vertices has derivative zero at a sphere polygon, the polygon is stationary for the polygon
energy along every differentiable curve of sphere polygons. -/

@[expose] public section

namespace Finsler.PolygonEnergyGlobal

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.SphereDistance
open Set Filter
open scoped Topology ContDiff

noncomputable section

variable {n : ℕ}

theorem norm_coe (P : Sphere n) : ‖(P : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp P.2

/-- For nearby points of the sphere the Finsler distance changes by at most a multiple of the
ambient distances. -/
theorem exists_dist_lipschitz (F : ReversibleMetric n) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ P Q P' Q' : Sphere n, ‖(P' : Ambient n) - P‖ ≤ 1 →
      ‖(Q' : Ambient n) - Q‖ ≤ 1 →
      |SphereDistance.dist F P' Q' - SphereDistance.dist F P Q| ≤
        K * (‖(P' : Ambient n) - P‖ + ‖(Q' : Ambient n) - Q‖) := by
  obtain ⟨K, hK, hup⟩ := exists_dist_upper F
  refine ⟨K, hK, ?_⟩
  intro P Q P' Q' hP hQ
  have hP' : ‖(P : Ambient n) - P'‖ ≤ 1 := by rwa [norm_sub_rev]
  have hQ' : ‖(Q : Ambient n) - Q'‖ ≤ 1 := by rwa [norm_sub_rev]
  have h1 := dist_triangle_sphere F hn (norm_coe P') (norm_coe P) (norm_coe Q')
  have h2 := dist_triangle_sphere F hn (norm_coe P) (norm_coe Q) (norm_coe Q')
  have h3 := dist_triangle_sphere F hn (norm_coe P) (norm_coe P') (norm_coe Q)
  have h4 := dist_triangle_sphere F hn (norm_coe P') (norm_coe Q') (norm_coe Q)
  have u1 := hup P' P (norm_coe P') (norm_coe P) hP'
  have u2 := hup Q Q' (norm_coe Q) (norm_coe Q') hQ
  have u3 := hup P P' (norm_coe P) (norm_coe P') hP
  have u4 := hup Q' Q (norm_coe Q') (norm_coe Q) hQ'
  rw [norm_sub_rev] at u1 u4
  rw [abs_le]
  constructor <;> nlinarith

/-- The Finsler distance is continuous on pairs of sphere points. -/
theorem dist_continuous (F : ReversibleMetric n) (hn : 1 ≤ n) :
    Continuous fun x : Sphere n × Sphere n =>
      SphereDistance.dist F (x.1 : Ambient n) (x.2 : Ambient n) := by
  obtain ⟨K, hK, hlip⟩ := exists_dist_lipschitz F hn
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun x : Sphere n × Sphere n =>
      K * (‖(x.1 : Ambient n) - x₀.1‖ + ‖(x.2 : Ambient n) - x₀.2‖) :=
    continuous_const.mul
      (((continuous_subtype_val.comp continuous_fst).sub continuous_const).norm.add
        ((continuous_subtype_val.comp continuous_snd).sub continuous_const).norm)
  have hlim := hc.tendsto x₀
  simp only [sub_self, norm_zero, add_zero, mul_zero] at hlim
  have h1 : ∀ᶠ x : Sphere n × Sphere n in 𝓝 x₀, ‖(x.1 : Ambient n) - x₀.1‖ ≤ 1 := by
    have hc1 : Continuous fun x : Sphere n × Sphere n => ‖(x.1 : Ambient n) - x₀.1‖ :=
      ((continuous_subtype_val.comp continuous_fst).sub continuous_const).norm
    have := hc1.tendsto x₀
    simp only [sub_self, norm_zero] at this
    exact (this.eventually (gt_mem_nhds (zero_lt_one' ℝ))).mono fun x hx => hx.le
  have h2 : ∀ᶠ x : Sphere n × Sphere n in 𝓝 x₀, ‖(x.2 : Ambient n) - x₀.2‖ ≤ 1 := by
    have hc2 : Continuous fun x : Sphere n × Sphere n => ‖(x.2 : Ambient n) - x₀.2‖ :=
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const).norm
    have := hc2.tendsto x₀
    simp only [sub_self, norm_zero] at this
    exact (this.eventually (gt_mem_nhds (zero_lt_one' ℝ))).mono fun x hx => hx.le
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hlim
  filter_upwards [h1, h2] with x hx1 hx2
  rw [Real.norm_eq_abs]
  exact hlip x₀.1 x₀.2 x.1 x.2 hx1 hx2

/-- The minimal energy is continuous on pairs of sphere points. -/
theorem minEnergy_continuous (F : ReversibleMetric n) (hn : 1 ≤ n) :
    Continuous fun x : Sphere n × Sphere n => minEnergy F (x.1 : Ambient n) (x.2 : Ambient n) := by
  exact ((dist_continuous F hn).pow 2).congr fun x => dist_sq F _ _

/-- The polygon energy is continuous on sphere polygons. -/
theorem polyEnergy_continuous (F : ReversibleMetric n) (hn : 1 ≤ n) (N : ℕ) :
    Continuous fun q : ZMod N → Sphere n => polyEnergy F N fun i => (q i : Ambient n) := by
  unfold polyEnergy
  refine continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
  have hpair : Continuous fun q : ZMod N → Sphere n => (q (k : ZMod N), q ((k : ZMod N) + 1)) :=
    (continuous_apply (k : ZMod N)).prodMk (continuous_apply ((k : ZMod N) + 1))
  exact (minEnergy_continuous F hn).comp hpair

/-- A polygon of energy at most b has edges of squared length at most b / (c N). -/
theorem exists_edge_bound (F : ReversibleMetric n) (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n) (b : ℝ),
      polyEnergy F N (fun i => (q i : Ambient n)) ≤ b →
      ∀ j : ZMod N, N * (c * ‖(q (j + 1) : Ambient n) - q j‖ ^ 2) ≤ b := by
  obtain ⟨c, hc, hlow⟩ := exists_minEnergy_lower F
  refine ⟨c, hc, ?_⟩
  intro N _ q b hb j
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hterm : ∀ k ∈ Finset.range N,
      0 ≤ minEnergy F (q (k : ZMod N) : Ambient n) (q ((k : ZMod N) + 1)) :=
    fun k _ => minEnergy_nonneg F _ _
  have hj : j.val ∈ Finset.range N := Finset.mem_range.mpr (ZMod.val_lt j)
  have hsingle := Finset.single_le_sum hterm hj
  have hjc : ((j.val : ℕ) : ZMod N) = j := ZMod.natCast_zmod_val j
  rw [hjc] at hsingle
  have hl := hlow (q j : Ambient n) (q (j + 1) : Ambient n)
    (pathsBetween_nonempty hn (norm_coe (q j)) (norm_coe (q (j + 1))))
  unfold polyEnergy at hb
  calc (N : ℝ) * (c * ‖(q (j + 1) : Ambient n) - q j‖ ^ 2)
      ≤ N * minEnergy F (q j : Ambient n) (q (j + 1)) := mul_le_mul_of_nonneg_left hl hN
    _ ≤ N * ∑ k ∈ Finset.range N,
        minEnergy F (q (k : ZMod N) : Ambient n) (q ((k : ZMod N) + 1)) :=
          mul_le_mul_of_nonneg_left hsingle hN
    _ ≤ b := hb

/-- Normalization is invariant under positive rescaling. -/
theorem normalize_smul {x : Ambient n} (hx : x ≠ 0) {l : ℝ} (hl : 0 < l) :
    normalize (l • x) = normalize x := by
  have hlx : l • x ≠ 0 := smul_ne_zero hl.ne' hx
  have e1 : (normalize (l • x) : Ambient n) = ‖l • x‖⁻¹ • (l • x) :=
    congrArg Subtype.val (normalize_coe (⟨l • x, hlx⟩ : nonzeroAmbient n))
  have e2 : (normalize x : Ambient n) = ‖x‖⁻¹ • x :=
    congrArg Subtype.val (normalize_coe (⟨x, hx⟩ : nonzeroAmbient n))
  apply Subtype.ext
  rw [e1, e2, norm_smul, Real.norm_of_nonneg hl.le, smul_smul, mul_inv, mul_assoc,
    mul_comm ‖x‖⁻¹ l, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]

/-- The polygon energy with normalized vertices does not change when one vertex is rescaled by
a factor close to 1. -/
theorem polyEnergyN_rescale (F : ReversibleMetric n) (N : ℕ) (Q : ZMod N → Ambient n)
    (hQ : ∀ i, Q i ≠ 0) (j : ZMod N) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      polyEnergyN F N (Q + s • (Pi.single j (Q j) : ZMod N → Ambient n)) = polyEnergyN F N Q := by
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < 1 + s := by
    have hc : Continuous fun s : ℝ => 1 + s := continuous_const.add continuous_id
    have h := hc.tendsto 0
    rw [add_zero] at h
    exact h.eventually (lt_mem_nhds zero_lt_one)
  filter_upwards [hpos] with s hs
  have hvert : ∀ i : ZMod N, normalize ((Q + s • (Pi.single j (Q j) : ZMod N → Ambient n)) i) =
      normalize (Q i) := by
    intro i
    by_cases hi : i = j
    · subst hi
      have he : (Q + s • (Pi.single i (Q i) : ZMod N → Ambient n)) i = (1 + s) • Q i := by
        rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, add_smul, one_smul]
      rw [he, normalize_smul (hQ i) hs]
    · have he : (Q + s • (Pi.single j (Q j) : ZMod N → Ambient n)) i = Q i := by
        rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, add_zero]
      rw [he]
  unfold polyEnergyN ambientMinEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [hvert]

/-- If the polygon energy with normalized vertices has derivative zero at a sphere polygon, the
polygon is stationary for the polygon energy along every differentiable curve of sphere
polygons. -/
theorem polyCritical_of_hasFDerivAt (F : ReversibleMetric n) {N : ℕ} [NeZero N]
    {q : ZMod N → Sphere n}
    (h : HasFDerivAt (polyEnergyN F N) (0 : (ZMod N → Ambient n) →L[ℝ] ℝ)
      (fun i => (q i : Ambient n))) : PolyCritical F N q := by
  intro c c' hc0 hcn hcd
  have hcomp : HasDerivAt (fun r : ℝ => polyEnergyN F N (c r))
      ((0 : (ZMod N → Ambient n) →L[ℝ] ℝ) c') (0 : ℝ) := by
    have h' : HasFDerivAt (polyEnergyN F N) (0 : (ZMod N → Ambient n) →L[ℝ] ℝ) (c 0) := by
      rw [hc0]
      exact h
    exact h'.comp_hasDerivAt (0 : ℝ) hcd
  rw [zero_apply] at hcomp
  have he : (fun r => polyEnergy F N (c r)) = fun r => polyEnergyN F N (c r) := by
    funext r
    exact (polyEnergyN_eq F N (hcn r)).symm
  rw [he]
  exact hcomp

end

end Finsler.PolygonEnergyGlobal
