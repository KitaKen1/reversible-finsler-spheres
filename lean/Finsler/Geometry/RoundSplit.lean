module

public import Finsler.Geometry.RoundChart
public import Finsler.Geometry.FrameCoordinates
public import Finsler.Analysis.FibreQuadratic

/-! The split descent estimate in the chart around the regular m-gons.

Let Ψ = pen ∘ chart. Along the critical manifold (z ∈ V₂, ξ = 0) the fibre derivative of Ψ
vanishes and its second fibre derivative is the second derivative of pen on the linear part of
the chart. The fibre form −D²pen(lin ξ, lin (J z ξ)) is continuous in (z, ξ), homogeneous of
degree two and positive off ξ = 0 (`fibForm_pos`), so by compactness of V₂ × (unit sphere) it is
at least 2c ‖ξ‖². By the expansion along the fibres there is R > 0 with

  DΨ(z, ξ)(0, J z ξ) ≤ −c ‖ξ‖²   (z ∈ V₂, ‖ξ‖ ≤ R),

which makes the split field (0, J z ξ) a strict descent direction off the critical manifold.
Moreover Ψ grows at most quadratically along the fibres from its value (2πm)². -/

@[expose] public section

namespace Finsler.RoundSplit

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon Finsler.RoundHessian
open Finsler.RoundModes Finsler.RoundNondeg Finsler.RoundCoords Finsler.RoundSpectral
open Finsler.RoundPenHess Finsler.RoundPenForm Finsler.AmbientPenalty Finsler.PolygonSmooth
open Finsler.RoundChart Finsler.FrameCoordinates Finsler.NormalExpansion Finsler.FibreQuadratic
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

/-! ### Compactness -/

section Compact

variable {E₀ X : Type*} [NormedAddCommGroup E₀] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- A continuous function, homogeneous of degree two in the fibre and positive off the zero
section over a compact set, is uniformly positive there. -/
theorem exists_uniform_pos {K : Set E₀} (hK : IsCompact K) {F : E₀ → X → ℝ}
    (hc : ContinuousOn (fun p : E₀ × X => F p.1 p.2) (K ×ˢ univ))
    (hhom : ∀ z ξ (t : ℝ), F z (t • ξ) = t ^ 2 * F z ξ)
    (hpos : ∀ z ∈ K, ∀ ξ, ξ ≠ 0 → 0 < F z ξ) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ ξ, c * ‖ξ‖ ^ 2 ≤ F z ξ := by
  have hS : IsCompact (K ×ˢ sphere (0 : X) 1) := hK.prod (isCompact_sphere 0 1)
  by_cases hne : (K ×ˢ sphere (0 : X) 1).Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hne
      (hc.mono (prod_mono subset_rfl (subset_univ _)))
    have hp0 : p₀.2 ≠ 0 := by
      intro h
      have := hp₀.2
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨F p₀.1 p₀.2, hpos _ hp₀.1 _ hp0, fun z hz ξ => ?_⟩
    by_cases hξ : ξ = 0
    · subst hξ
      have h0 := hhom z 0 0
      rw [zero_smul] at h0
      rw [h0, norm_zero]
      simp
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      have hmem : (z, ‖ξ‖⁻¹ • ξ) ∈ K ×ˢ sphere (0 : X) 1 := by
        refine ⟨hz, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : F p₀.1 p₀.2 ≤ F z (‖ξ‖⁻¹ • ξ) := hmin hmem
      have h2 := hhom z (‖ξ‖⁻¹ • ξ) ‖ξ‖
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at h2
      rw [h2, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · refine ⟨1, one_pos, fun z hz ξ => ?_⟩
    by_cases hξ : ξ = 0
    · subst hξ
      have h0 := hhom z 0 0
      rw [zero_smul] at h0
      rw [h0, norm_zero]
      simp
    · exfalso
      apply hne
      refine ⟨(z, ‖ξ‖⁻¹ • ξ), hz, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]

/-- A continuous function, homogeneous of degree one in the fibre over a compact set, is
bounded by a multiple of the norm. -/
theorem exists_uniform_bound {K : Set E₀} (hK : IsCompact K) {F : E₀ → X → ℝ}
    (hc : ContinuousOn (fun p : E₀ × X => F p.1 p.2) (K ×ˢ univ))
    (hhom : ∀ z ξ (t : ℝ), 0 ≤ t → F z (t • ξ) = t * F z ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ ξ, F z ξ ≤ C * ‖ξ‖ := by
  have hS : IsCompact (K ×ˢ sphere (0 : X) 1) := hK.prod (isCompact_sphere 0 1)
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn (f := fun p : E₀ × X => F p.1 p.2)
    (hc.mono (prod_mono subset_rfl (subset_univ _)))
  refine ⟨max C₀ 0, le_max_right _ _, fun z hz ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 := hhom z 0 0 le_rfl
    rw [zero_smul, zero_mul] at h0
    rw [h0, norm_zero, mul_zero]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hmem : (z, ‖ξ‖⁻¹ • ξ) ∈ K ×ˢ sphere (0 : X) 1 := by
      refine ⟨hz, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 : ‖F z (‖ξ‖⁻¹ • ξ)‖ ≤ C₀ := hC₀ _ hmem
    have h2 := hhom z (‖ξ‖⁻¹ • ξ) ‖ξ‖ (norm_nonneg _)
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at h2
    have h3 : F z (‖ξ‖⁻¹ • ξ) ≤ max C₀ 0 :=
      (le_abs_self _).trans ((Real.norm_eq_abs (F z (‖ξ‖⁻¹ • ξ))).symm.le.trans
        (h1.trans (le_max_left _ _)))
    calc F z ξ = ‖ξ‖ * F z (‖ξ‖⁻¹ • ξ) := h2
      _ ≤ ‖ξ‖ * max C₀ 0 := mul_le_mul_of_nonneg_left h3 (norm_nonneg ξ)
      _ = max C₀ 0 * ‖ξ‖ := mul_comm _ _

end Compact

variable {n : ℕ} {N : ℕ} [NeZero N] {m M : ℕ} (hNM : N = 2 * M + 1) (hm : 0 < m) (hmM : m < M)
include hNM hm hmM

/-! ### Continuity of the fibre form -/

theorem lin_continuous : Continuous fun p : (Ambient n × Ambient n) × Fib n N m => lin m p.1 p.2 := by
  have hsub : Continuous (fun p : (Ambient n × Ambient n) × Fib n N m =>
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  rw [continuous_pi_iff]
  intro i
  have hi : Continuous (fun p : (Ambient n × Ambient n) × Fib n N m =>
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) i) :=
    (continuous_apply i).comp hsub
  simp only [lin_apply, Pi.add_apply, regular, circ]
  fun_prop

theorem negV_continuous : Continuous fun p : (Ambient n × Ambient n) × (ZMod N → Ambient n) =>
    negV m p.1 p.2 := by
  have hl : Continuous fun p : (Ambient n × Ambient n) × (ZMod N → Ambient n) => low m p.2 := by
    have hlc : Continuous (low (n := n) (N := N) m) := by
      have hlin : IsLinearMap ℝ (low (n := n) (N := N) m) :=
        ⟨low_add m, fun r V => low_smul m r V⟩
      exact (hlin.mk' _).continuous_of_finiteDimensional
    exact hlc.comp continuous_snd
  rw [continuous_pi_iff]
  intro i
  have hli : Continuous fun p : (Ambient n × Ambient n) × (ZMod N → Ambient n) => low m p.2 i :=
    (continuous_apply i).comp hl
  have hP : Continuous fun q : (Ambient n × Ambient n) × Ambient n => projW q.1 q.2 := by
    simp only [projW_apply]
    fun_prop
  exact hP.comp (continuous_fst.prodMk hli)

theorem J_continuous : Continuous fun p : (Ambient n × Ambient n) × Fib n N m =>
    J hm (two_m_lt_N hNM hmM) p.1 p.2 := by
  have hV : Continuous fun p : (Ambient n × Ambient n) × Fib n N m =>
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hneg : Continuous fun p : (Ambient n × Ambient n) × Fib n N m =>
      negV m p.1 ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) :=
    Continuous.comp (g := fun q : (Ambient n × Ambient n) × (ZMod N → Ambient n) => negV m q.1 q.2)
      (f := fun p : (Ambient n × Ambient n) × Fib n N m =>
        (p.1, ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n)))
      (negV_continuous hNM hm hmM) (continuous_fst.prodMk hV)
  have h1 : Continuous fun p : (Ambient n × Ambient n) × Fib n N m =>
      (J hm (two_m_lt_N hNM hmM) p.1 p.2).1 := by
    have e : (fun p : (Ambient n × Ambient n) × Fib n N m => (J hm (two_m_lt_N hNM hmM) p.1 p.2).1) =
        fun p => -p.2.1 := funext fun p => (J_apply hm (two_m_lt_N hNM hmM) p.1 p.2).1
    rw [e]
    exact (continuous_fst.comp continuous_snd).neg
  have h2 : Continuous fun p : (Ambient n × Ambient n) × Fib n N m =>
      (J hm (two_m_lt_N hNM hmM) p.1 p.2).2 := by
    apply continuous_induced_rng.mpr
    have e : (Subtype.val ∘ fun p : (Ambient n × Ambient n) × Fib n N m =>
        (J hm (two_m_lt_N hNM hmM) p.1 p.2).2) = fun p =>
        (2 : ℝ) • negV m p.1 ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) -
          ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) :=
      funext fun p => (J_apply hm (two_m_lt_N hNM hmM) p.1 p.2).2
    rw [e]
    exact (hneg.const_smul (2 : ℝ)).sub hV
  exact h1.prodMk h2

/-- The second derivative of pen is continuous along the regular polygons of pairs. -/
theorem hess_continuousOn : ContinuousOn
    (fun z : Ambient n × Ambient n =>
      fderiv ℝ (fderiv ℝ (pen (roundMetric n) N 1)) (regular N m z.1 z.2)) V2 := by
  have hmN : 2 * m < N := two_m_lt_N hNM hmM
  have hreg : Continuous fun z : Ambient n × Ambient n => regular N m z.1 z.2 := by
    rw [continuous_pi_iff]
    intro i
    simp only [regular, circ]
    fun_prop
  have hgood : ∀ z ∈ V2 (n := n), regular N m z.1 z.2 ∈ good N := fun z hz =>
    regular_mem_good hm hmN hz.1 hz.2.1 hz.2.2
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (pen (roundMetric n) N 1))) (good (n := n) N) := by
    have hC : ContDiffOn ℝ ∞ (pen (roundMetric n) N 1) (good (n := n) N) :=
      fun P hP => (pen_contDiffAt hP 1).contDiffWithinAt
    have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (pen (roundMetric n) N 1)) (good (n := n) N) :=
      hC.fderiv_of_isOpen (m := ∞) good_isOpen (by simp)
    exact (h1.fderiv_of_isOpen (m := ∞) good_isOpen (by simp)).continuousOn
  exact hcont.comp hreg.continuousOn hgood

theorem fibForm_continuousOn :
    ContinuousOn (fun p : (Ambient n × Ambient n) × Fib n N m => fibForm m hNM hm hmM p.1 p.2)
      (V2 ×ˢ univ) := by
  have h1 := (hess_continuousOn hNM hm hmM).comp continuousOn_fst
    (fun (p : (Ambient n × Ambient n) × Fib n N m) (hp : p ∈ V2 ×ˢ univ) => hp.1)
  have h2 := (lin_continuous (n := n) hNM hm hmM).continuousOn (s := V2 ×ˢ univ)
  have h3 : ContinuousOn (fun p : (Ambient n × Ambient n) × Fib n N m =>
      lin m p.1 (J hm (two_m_lt_N hNM hmM) p.1 p.2)) (V2 ×ˢ univ) := by
    have := (lin_continuous (n := n) hNM hm hmM).comp
      (continuous_fst.prodMk (J_continuous (n := n) hNM hm hmM))
    exact this.continuousOn
  have h4 := (h1.clm_apply h2).clm_apply h3
  unfold fibForm
  exact h4.neg

theorem fibForm_hom (z : Ambient n × Ambient n) (ξ : Fib n N m) (t : ℝ) :
    fibForm m hNM hm hmM z (t • ξ) = t ^ 2 * fibForm m hNM hm hmM z ξ := by
  unfold fibForm
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The fibre form is uniformly positive on the critical manifold.** -/
theorem exists_fibForm_bound : ∃ c : ℝ, 0 < c ∧ ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m,
    c * ‖ξ‖ ^ 2 ≤ fibForm m hNM hm hmM z ξ := by
  refine exists_uniform_pos isCompact_V2 (fibForm_continuousOn hNM hm hmM)
    (fibForm_hom hNM hm hmM) fun z hz ξ hξ => ?_
  obtain ⟨h1, h2⟩ := fibForm_pos hNM hm hmM hz ξ
  exact lt_of_le_of_ne h1 fun h => hξ (h2 h.symm)

theorem exists_J_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m,
    ‖J hm (two_m_lt_N hNM hmM) z ξ‖ ≤ C * ‖ξ‖ := by
  refine exists_uniform_bound isCompact_V2 ?_ fun z ξ t ht => ?_
  · exact (continuous_norm.comp (J_continuous hNM hm hmM)).continuousOn
  · rw [map_smul, norm_smul, Real.norm_of_nonneg ht]

/-! ### The penalized energy in the chart -/

variable (m) in
/-- The penalized energy in the chart. -/
def Psi (p : (Ambient n × Ambient n) × Fib n N m) : ℝ := pen (roundMetric n) N 1 (chart m p)

variable (m) in
/-- The chart points with good image polygons. -/
def dom : Set ((Ambient n × Ambient n) × Fib n N m) := chart m ⁻¹' good N

omit hNM hm hmM in
theorem dom_isOpen : IsOpen (dom (n := n) (N := N) m) :=
  good_isOpen.preimage (chart_contDiff (n := n) (N := N) m).continuous

omit hNM hm hmM in
theorem Psi_contDiffOn : ContDiffOn ℝ ∞ (Psi (n := n) (N := N) m) (dom m) := fun p hp =>
  ((pen_contDiffAt hp 1).comp p (chart_contDiff (n := n) (N := N) m).contDiffAt).contDiffWithinAt

theorem zero_mem_dom {z : Ambient n × Ambient n} (hz : z ∈ V2) :
    (z, (0 : Fib n N m)) ∈ dom (n := n) (N := N) m := by
  change chart m (z, 0) ∈ good N
  rw [chart_zero]
  exact regular_mem_good hm (two_m_lt_N hNM hmM) hz.1 hz.2.1 hz.2.2

/-- The derivative of Ψ vanishes along the critical manifold. -/
theorem fderiv_Psi_zero {z : Ambient n × Ambient n} (hz : z ∈ V2) :
    fderiv ℝ (Psi (n := n) (N := N) m) (z, 0) = 0 := by
  have hmN := two_m_lt_N hNM hmM
  have hpen : DifferentiableAt ℝ (pen (roundMetric n) N 1) (chart m (z, (0 : Fib n N m))) := by
    rw [chart_zero]
    exact (pen_contDiffAt (regular_mem_good hm hmN hz.1 hz.2.1 hz.2.2) 1).differentiableAt
      (by simp)
  have hch : DifferentiableAt ℝ (chart (n := n) (N := N) m) (z, 0) :=
    (chart_contDiff (n := n) (N := N) m).differentiable (by simp) _
  have h := fderiv_comp (z, (0 : Fib n N m)) hpen hch
  change fderiv ℝ (pen (roundMetric n) N 1 ∘ chart m) (z, 0) = 0
  rw [h, chart_zero, fderiv_pen_regular hm hmN hz.1 hz.2.1 hz.2.2]
  simp

/-- The second fibre derivative of Ψ along the critical manifold. -/
theorem sndDeriv_Psi_fibre {z : Ambient n × Ambient n} (hz : z ∈ V2) (ξ η : Fib n N m) :
    fderiv ℝ (fderiv ℝ (Psi (n := n) (N := N) m)) (z, 0) (0, ξ) (0, η) =
      fderiv ℝ (fderiv ℝ (pen (roundMetric n) N 1)) (regular N m z.1 z.2) (lin m z ξ)
        (lin m z η) := by
  have hmN := two_m_lt_N hNM hmM
  set L := ContinuousLinearMap.inr ℝ (Ambient n × Ambient n) (Fib n N m)
  have hPsi2 : ContDiffAt ℝ 2 (Psi (n := n) (N := N) m) ((z, 0) + L 0) := by
    rw [map_zero, add_zero]
    exact ((Psi_contDiffOn (m := m)).contDiffAt (dom_isOpen.mem_nhds
      (zero_mem_dom hNM hm hmM hz))).of_le (by simp)
  have h1 := sndDeriv_comp_affine (z, (0 : Fib n N m)) L hPsi2 ξ η
  rw [map_zero, add_zero] at h1
  have e : (fun x => Psi (n := n) (N := N) m ((z, 0) + L x)) =
      fun x => pen (roundMetric n) N 1 (regular N m z.1 z.2 + lin m z x) := by
    funext x
    simp [Psi, chart, L]
  rw [e] at h1
  have hpen2 : ContDiffAt ℝ 2 (pen (roundMetric n) N 1) (regular N m z.1 z.2 + lin m z 0) := by
    rw [map_zero, add_zero]
    exact (pen_contDiffAt (regular_mem_good hm hmN hz.1 hz.2.1 hz.2.2) 1).of_le (by simp)
  have h2 := sndDeriv_comp_affine (regular N m z.1 z.2) (lin m z) hpen2 ξ η
  rw [map_zero, add_zero] at h2
  rw [← h2, h1]
  rfl

/-- **The split descent estimate.** -/
theorem exists_split_descent : ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m,
    ‖ξ‖ ≤ R → (z, ξ) ∈ dom (n := n) (N := N) m ∧
      fderiv ℝ (Psi (n := n) (N := N) m) (z, ξ) (0, J hm (two_m_lt_N hNM hmM) z ξ) ≤
        -c * ‖ξ‖ ^ 2 := by
  obtain ⟨c₀, hc₀, hform⟩ := exists_fibForm_bound (n := n) hNM hm hmM
  obtain ⟨CJ, hCJ, hJb⟩ := exists_J_bound (n := n) hNM hm hmM
  have hε : 0 < c₀ / (2 * (CJ + 1)) := by positivity
  obtain ⟨R, hR, hexp⟩ := exists_fibre_expansion (dom_isOpen (n := n) (N := N) (m := m))
    ((Psi_contDiffOn (m := m)).of_le (by simp)) isCompact_V2
    (fun z hz => zero_mem_dom hNM hm hmM hz)
    (fun z hz w => by rw [fderiv_Psi_zero hNM hm hmM hz]; rfl) hε
  refine ⟨R, c₀ / 2, hR, by positivity, fun z hz ξ hξ => ⟨(hexp z hz ξ hξ).1, ?_⟩⟩
  have h1 := (abs_le.mp ((hexp z hz ξ hξ).2 (J hm (two_m_lt_N hNM hmM) z ξ))).2
  have h2 : fderiv ℝ (fderiv ℝ (Psi (n := n) (N := N) m)) (z, 0) (0, ξ)
      (0, J hm (two_m_lt_N hNM hmM) z ξ) = -fibForm m hNM hm hmM z ξ := by
    rw [sndDeriv_Psi_fibre hNM hm hmM hz]
    unfold fibForm
    ring
  rw [h2] at h1
  have h3 := hform z hz ξ
  have h4 := hJb z hz ξ
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have h5 : c₀ / (2 * (CJ + 1)) * ‖ξ‖ * ‖J hm (two_m_lt_N hNM hmM) z ξ‖ ≤ c₀ / 2 * ‖ξ‖ ^ 2 := by
    calc c₀ / (2 * (CJ + 1)) * ‖ξ‖ * ‖J hm (two_m_lt_N hNM hmM) z ξ‖
        ≤ c₀ / (2 * (CJ + 1)) * ‖ξ‖ * (CJ * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = c₀ / 2 * ‖ξ‖ ^ 2 * (CJ / (CJ + 1)) := by
          field_simp
      _ ≤ c₀ / 2 * ‖ξ‖ ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]
          linarith
      _ = c₀ / 2 * ‖ξ‖ ^ 2 := mul_one _
  linarith

/-- **Quadratic growth along the fibres.** -/
theorem exists_quadratic : ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m,
    ‖ξ‖ ≤ R → (z, ξ) ∈ dom (n := n) (N := N) m ∧
      |Psi (n := n) (N := N) m (z, ξ) - (2 * π * m) ^ 2| ≤ C * ‖ξ‖ ^ 2 := by
  have hmN := two_m_lt_N hNM hmM
  obtain ⟨R, C, hR, hC, h⟩ := exists_fibre_quadratic (dom_isOpen (n := n) (N := N) (m := m))
    ((Psi_contDiffOn (m := m)).of_le (by simp)) isCompact_V2
    (fun z hz => zero_mem_dom hNM hm hmM hz)
    (fun z hz w => by rw [fderiv_Psi_zero hNM hm hmM hz]; rfl)
  refine ⟨R, C, hR, hC, fun z hz ξ hξ => ⟨(h z hz ξ hξ).1, ?_⟩⟩
  have hval : Psi (n := n) (N := N) m (z, 0) = (2 * π * m) ^ 2 := by
    unfold Psi pen
    rw [chart_zero, polyEnergyN_eq _ _ (norm_regular hz.1 hz.2.1 hz.2.2),
      polyEnergy_regular hmN hz.1 hz.2.1 hz.2.2]
    have hl : logPen (regular N m z.1 z.2) = 0 := by
      unfold logPen
      simp [norm_regular hz.1 hz.2.1 hz.2.2]
    rw [hl, mul_zero, add_zero]
  rw [← hval]
  exact (h z hz ξ hξ).2

end

end Finsler.RoundSplit
