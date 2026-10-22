module

public import Finsler.Geometry.RoundModel
public import Finsler.Analysis.LogCutoff

/-! The deformation of the penalized energy to the model near the regular m-gons, in the chart.

With the logarithmic cutoff χ = Φ ∘ sqF (Φ = 1 on [0, r²], 0 beyond r² e^λ) the deformed
function is G = Ψ + χ (model − Ψ). Along the split field (0, J z ξ):

* DΨ ≤ −c₁ ‖ξ‖² ≤ −(c₁ / C_F) sqF (split descent estimate, sqF ≤ C_F ‖ξ‖²);
* D model = −2 sqF;
* |model − Ψ| ≤ sqF + C₂ ‖ξ‖² ≤ (1 + C₂ / c_F) sqF (quadratic growth, sqF ≥ c_F ‖ξ‖²);
* |Dχ| ≤ 2M / λ, because |D sqF (0, Jξ)| ≤ 2 sqF.

For λ large the deformation inequality gives DG(z, ξ)(0, Jξ) ≤ −c sqF(z, ξ) on ‖ξ‖ ≤ R, with c
independent of r. Where χ = 1 the deformed function is the model. -/

@[expose] public section

namespace Finsler.RoundDeform

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon Finsler.RoundCoords
open Finsler.RoundSpectral Finsler.RoundPenHess Finsler.RoundPenForm Finsler.AmbientPenalty
open Finsler.PolygonSmooth Finsler.RoundChart Finsler.RoundSplit Finsler.RoundLabel
open Finsler.RoundModel Finsler.LogCutoff
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m M : ℕ}

/-- The cutoff in the chart. -/
def chi (r lam : ℝ) (p : (Ambient n × Ambient n) × Fib n N m) : ℝ := logCut r lam (sqF p)

variable (m) in
/-- The deformed function in the chart. -/
def Gdef (r lam : ℝ) (p : (Ambient n × Ambient n) × Fib n N m) : ℝ :=
  Psi m p + chi r lam p * (model m p - Psi m p)

theorem chi_contDiff {r lam : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) :
    ContDiff ℝ ∞ (chi (n := n) (N := N) (m := m) r lam) :=
  logCut_comp_contDiff hr hlam (sqF_contDiff (n := n) (N := N) (m := m)) sqF_nonneg

theorem Gdef_of_chi_one {r lam : ℝ} {p : (Ambient n × Ambient n) × Fib n N m}
    (h : chi r lam p = 1) : Gdef m r lam p = model m p := by
  unfold Gdef
  rw [h, one_mul, add_sub_cancel]

theorem chi_one {r lam : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) {p : (Ambient n × Ambient n) × Fib n N m}
    (hp : sqF p ≤ r ^ 2) : chi r lam p = 1 :=
  logCut_of_le hr hlam (sqF_nonneg p) hp

theorem chi_zero {r lam : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) {p : (Ambient n × Ambient n) × Fib n N m}
    (hp : r ^ 2 * Real.exp lam ≤ sqF p) : chi r lam p = 0 :=
  logCut_of_ge hr hlam hp

theorem Gdef_of_chi_zero {r lam : ℝ} {p : (Ambient n × Ambient n) × Fib n N m}
    (h : chi r lam p = 0) : Gdef m r lam p = Psi m p := by
  unfold Gdef
  rw [h, zero_mul, add_zero]

variable (hNM : N = 2 * M + 1) (hm : 0 < m) (hmM : m < M)
include hNM hm hmM

/-- **The descent estimate of the deformed function.** -/
theorem exists_deform_descent : ∃ R c lam₀ : ℝ, 0 < R ∧ 0 < c ∧ 0 < lam₀ ∧
    ∀ r lam : ℝ, r ≠ 0 → lam₀ ≤ lam → ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R →
      (z, ξ) ∈ dom (n := n) (N := N) m ∧
      fderiv ℝ (Psi (n := n) (N := N) m) (z, ξ) (0, J hm (two_m_lt_N hNM hmM) z ξ) ≤
        -c * sqF (z, ξ) ∧
      fderiv ℝ (Gdef m r lam) (z, ξ) (0, J hm (two_m_lt_N hNM hmM) z ξ) ≤ -c * sqF (z, ξ) := by
  obtain ⟨R₁, c₁, hR₁, hc₁, hsplit⟩ := exists_split_descent (n := n) hNM hm hmM
  obtain ⟨R₂, C₂, hR₂, hC₂, hquad⟩ := exists_quadratic (n := n) hNM hm hmM
  obtain ⟨cF, CF, hcF, hCF, hF⟩ := exists_sqF_bounds (n := n) (N := N) (m := m)
  obtain ⟨Mt, hMt, hMb⟩ := exists_deriv_bound
  set c' := min (c₁ / (CF + 1)) 2 with hc'
  have hc'pos : 0 < c' := lt_min (by positivity) two_pos
  set C₁ := 1 + C₂ / cF with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  set lam₀ := 4 * Mt * C₁ / c' + 1 with hlam₀
  have hlam₀pos : 0 < lam₀ := by positivity
  refine ⟨min R₁ R₂, c' / 2, lam₀, lt_min hR₁ hR₂, half_pos hc'pos, hlam₀pos,
    fun r lam hr hlam z hz ξ hξ => ?_⟩
  have hlam : 0 < lam := hlam₀pos.trans_le hlam
  obtain ⟨hdom, hdΨ⟩ := hsplit z hz ξ (hξ.trans (min_le_left _ _))
  obtain ⟨-, hq⟩ := hquad z hz ξ (hξ.trans (min_le_right _ _))
  obtain ⟨hF1, hF2⟩ := hF z hz ξ
  have hmN := two_m_lt_N hNM hmM
  have hx0 : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
  have hsq := sqF_nonneg (z, ξ)
  -- the derivative of Ψ in terms of sqF
  have hΨ : fderiv ℝ (Psi (n := n) (N := N) m) (z, ξ) (0, J hm hmN z ξ) ≤ 0 - c' * sqF (z, ξ) := by
    have h1 : c' * sqF (z, ξ) ≤ c₁ / (CF + 1) * sqF (z, ξ) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hsq
    have h2 : c₁ / (CF + 1) * sqF (z, ξ) ≤ c₁ * ‖ξ‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : sqF (z, ξ) ≤ (CF + 1) * ‖ξ‖ ^ 2 := by nlinarith
      nlinarith
    linarith
  -- the derivative of the model
  have hM : fderiv ℝ (model (n := n) (N := N) m) (z, ξ) (0, J hm hmN z ξ) ≤ 0 - c' * sqF (z, ξ) := by
    rw [fderiv_model_J hm hmN hz]
    have : c' * sqF (z, ξ) ≤ 2 * sqF (z, ξ) := mul_le_mul_of_nonneg_right (min_le_right _ _) hsq
    linarith
  -- the difference of the model and Ψ
  have hδ : |model m (z, ξ) - Psi (n := n) (N := N) m (z, ξ)| ≤ C₁ * sqF (z, ξ) := by
    have h1 : |model m (z, ξ) - (2 * π * m) ^ 2| ≤ sqF (z, ξ) := by
      unfold model sqF
      rw [show (2 * π * m) ^ 2 - sqN (z, ξ) + sqP (z, ξ) - (2 * π * m) ^ 2 =
        sqP (z, ξ) - sqN (z, ξ) by ring, abs_le]
      have := sqN_nonneg (z, ξ)
      have := sqP_nonneg (z, ξ)
      constructor <;> linarith
    have h2 : C₂ * ‖ξ‖ ^ 2 ≤ C₂ / cF * sqF (z, ξ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcF]
      nlinarith
    calc |model m (z, ξ) - Psi (n := n) (N := N) m (z, ξ)|
        = |(model m (z, ξ) - (2 * π * m) ^ 2) - (Psi m (z, ξ) - (2 * π * m) ^ 2)| := by ring_nf
      _ ≤ |model m (z, ξ) - (2 * π * m) ^ 2| + |Psi m (z, ξ) - (2 * π * m) ^ 2| := abs_sub _ _
      _ ≤ sqF (z, ξ) + C₂ * ‖ξ‖ ^ 2 := add_le_add h1 hq
      _ ≤ C₁ * sqF (z, ξ) := by rw [hC₁]; nlinarith
  -- the derivative of the cutoff
  have hχ : |fderiv ℝ (chi (n := n) (N := N) (m := m) r lam) (z, ξ) (0, J hm hmN z ξ)| ≤
      2 * Mt / lam :=
    abs_fderiv_logCut_comp_le hr hlam zero_le_two hMb (sqF_contDiff (n := n) (N := N) (m := m))
      sqF_nonneg (z, ξ) (0, J hm hmN z ξ) (abs_fderiv_sqF_J hm hmN hz ξ)
  have hCε : C₁ * (2 * Mt / lam) ≤ c' / 2 := by
    have hl : 4 * Mt * C₁ / c' ≤ lam := by linarith
    rw [div_le_iff₀ hc'pos] at hl
    rw [mul_div_assoc', div_le_iff₀ hlam]
    nlinarith
  have hchi0 := logCut_nonneg r lam (sqF (z, ξ))
  have hchi1 := logCut_le_one r lam (sqF (z, ξ))
  have hd := deform_le hchi0 hchi1 hΨ hM hδ hχ hCε hsq
  have hhalf : c' / 2 * sqF (z, ξ) ≤ c' * sqF (z, ξ) :=
    mul_le_mul_of_nonneg_right (half_le_self hc'pos.le) hsq
  refine ⟨hdom, by linarith, ?_⟩
  have hΨd : DifferentiableAt ℝ (Psi (n := n) (N := N) m) (z, ξ) :=
    ((Psi_contDiffOn (m := m)).contDiffAt (dom_isOpen.mem_nhds hdom)).differentiableAt (by simp)
  have hMd := (model_contDiff (n := n) (N := N) (m := m)).differentiable (by simp) (z, ξ)
  have hχd := (chi_contDiff (n := n) (N := N) (m := m) hr hlam).differentiable (by simp) (z, ξ)
  have hG := fderiv_deform hΨd hMd hχd (0, J hm hmN z ξ)
  change fderiv ℝ (fun y => Psi m y + chi r lam y * (model m y - Psi m y)) (z, ξ)
    (0, J hm hmN z ξ) ≤ _
  rw [hG]
  unfold chi at hd ⊢
  linarith

end

end Finsler.RoundDeform
