module

public import Finsler.Analysis.OperatorIndex
public import Finsler.Analysis.Hessian
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Comparison of the indices of two functions related by a section and a retraction. Let f₁ and
f₂ be functions on finite-dimensional real inner product spaces, C² at p₁ and p₂, with p₁
critical for f₁. Let R be differentiable at p₁ with R p₁ = p₂ and f₂ ∘ R = f₁ near p₁, and let
ρ be differentiable at p₂ with ρ p₂ = p₁ and f₁ ∘ ρ ≤ f₂ near p₂. Then p₂ is critical for f₂,
the second derivatives satisfy D²f₁(v, v) = D²f₂(DR v, DR v) and D²f₁(Dρ u, Dρ u) ≤ D²f₂(u, u),
and the Hessians of f₁ at p₁ and of f₂ at p₂ have the same negative index of inertia. The
situation is that of partial minimization: f₁ is the minimum of f₂ over the additional
variables, as for the polygon energies of a polygon and of its refinement. The proof uses the
second-order Taylor expansion at a critical point along curves; neither R nor ρ needs a second
derivative. -/

@[expose] public section

namespace Finsler.IndexComparison

open Filter Module QuadraticMap Finsler.OperatorIndex
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section

/-! ### The second-order expansion at a critical point -/

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second-order Taylor bound at a critical point of a C² function. -/
theorem taylor2_bound {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hx : fderiv ℝ f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : E, ‖h‖ < δ →
      |f (x + h) - f x - 1 / 2 * fderiv ℝ (fderiv ℝ f) x h h| ≤ ε * ‖h‖ ^ 2 := by
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h1 : ∀ᶠ y in 𝓝 x,
      ‖fderiv ℝ f y - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x (y - x)‖ ≤ ε * ‖y - x‖ :=
    hD.isLittleO.def hε
  have h2 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  refine ⟨δ, hδ, fun h hh => ?_⟩
  set B := fderiv ℝ (fderiv ℝ f) x with hB
  let g : ℝ → ℝ := fun s => f (x + s • h) - s * s / 2 * B h h
  have hsmul : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖s • h‖ ≤ ‖h‖ := by
    intro s hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg h)
      _ = ‖h‖ := one_mul _
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, dist (x + s • h) x < δ := by
    intro s hs
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (hsmul s hs).trans_lt hh
  have hg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g (fderiv ℝ f (x + s • h) h - s * B h h) (Set.Icc 0 1) s := by
    intro s hs
    have hd := (hball (hmem s hs)).2
    have hline : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      have h0 := ((hasDerivAt_id s).smul_const h).const_add x
      rwa [one_smul] at h0
    have h3 : HasDerivAt (fun s : ℝ => f (x + s • h)) (fderiv ℝ f (x + s • h) h) s :=
      hd.hasFDerivAt.comp_hasDerivAt s hline
    have h4 : HasDerivAt (fun s : ℝ => s * s / 2 * B h h) (s * B h h) s := by
      have h0 := (((hasDerivAt_id s).mul (hasDerivAt_id s)).div_const 2).mul_const (B h h)
      have e : (1 * id s + id s * 1) / 2 * B h h = s * B h h := by
        simp only [id]
        ring
      rw [e] at h0
      exact h0
    exact (h3.sub h4).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖fderiv ℝ f (x + s • h) h - s * B h h‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hs
    have hb := (hball (hmem s hs')).1
    rw [hx, sub_zero, add_sub_cancel_left] at hb
    have e : fderiv ℝ f (x + s • h) h - s * B h h = (fderiv ℝ f (x + s • h) - B (s • h)) h := by
      rw [map_smul]
      rfl
    rw [e]
    calc ‖(fderiv ℝ f (x + s • h) - B (s • h)) h‖
        ≤ ‖fderiv ℝ f (x + s • h) - B (s • h)‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖s • h‖ * ‖h‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg h)
      _ ≤ ε * ‖h‖ * ‖h‖ := by
          have h5 := hsmul s hs'
          gcongr
      _ = ε * ‖h‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hg hbound
  have e1 : g 1 - g 0 = f (x + h) - f x - 1 / 2 * B h h := by
    simp only [g, one_smul, zero_smul, add_zero]
    ring
  rw [← e1, ← Real.norm_eq_abs]
  exact hmv

/-- Along a curve through a critical point of a C² function, the increment divided by t² tends
to half the second derivative at the velocity. -/
theorem tendsto_div_sq {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hx : fderiv ℝ f x = 0)
    {γ : ℝ → E} {w : E} (hγ : HasDerivAt γ w 0) (hγ0 : γ 0 = x) :
    Tendsto (fun t : ℝ => (f (γ t) - f x) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (1 / 2 * fderiv ℝ (fderiv ℝ f) x w w)) := by
  set B := fderiv ℝ (fderiv ℝ f) x with hB
  have hk : Tendsto (fun t : ℝ => t⁻¹ • (γ t - x)) (𝓝[≠] 0) (𝓝 w) := by
    have h := hγ.tendsto_slope_zero
    simp only [zero_add, hγ0] at h
    exact h
  have hh : Tendsto (fun t : ℝ => γ t - x) (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto γ (𝓝 0) (𝓝 x) := by
      have h0 := hγ.continuousAt.tendsto
      rwa [hγ0] at h0
    have h' := h.sub_const x
    rw [sub_self] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun t : ℝ => 1 / 2 * B (t⁻¹ • (γ t - x)) (t⁻¹ • (γ t - x))) (𝓝[≠] 0)
      (𝓝 (1 / 2 * B w w)) := by
    have hc : Continuous fun u : E => B u u := B.continuous.clm_apply continuous_id
    exact ((hc.tendsto w).comp hk).const_mul (1 / 2)
  have hrem : Tendsto
      (fun t : ℝ => (f (γ t) - f x - 1 / 2 * B (γ t - x) (γ t - x)) / t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C := ‖w‖ + 1 with hC
    have hCpos : 0 < C := by positivity
    obtain ⟨δ, hδ, hb⟩ := taylor2_bound hf hx (ε := ε / (2 * C ^ 2)) (by positivity)
    have e1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖γ t - x‖ < δ :=
      (Metric.tendsto_nhds.mp hh δ hδ).mono fun t ht => by rwa [dist_zero_right] at ht
    have e2 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖t⁻¹ • (γ t - x)‖ < C :=
      (Metric.tendsto_nhds.mp hk 1 one_pos).mono fun t ht => by
        rw [dist_eq_norm] at ht
        have h0 := norm_sub_norm_le (t⁻¹ • (γ t - x)) w
        linarith
    have e3 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
    filter_upwards [e1, e2, e3] with t h1 h2 h3
    have hb' := hb (γ t - x) h1
    rw [add_sub_cancel] at hb'
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have hk2 : ‖γ t - x‖ ^ 2 = t ^ 2 * ‖t⁻¹ • (γ t - x)‖ ^ 2 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
      field_simp
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos ht2, div_lt_iff₀ ht2]
    have hC2 : ‖t⁻¹ • (γ t - x)‖ ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2.le 2
    calc |f (γ t) - f x - 1 / 2 * B (γ t - x) (γ t - x)|
        ≤ ε / (2 * C ^ 2) * ‖γ t - x‖ ^ 2 := hb'
      _ = ε / (2 * C ^ 2) * (t ^ 2 * ‖t⁻¹ • (γ t - x)‖ ^ 2) := by rw [hk2]
      _ ≤ ε / (2 * C ^ 2) * (t ^ 2 * C ^ 2) := by gcongr
      _ = ε / 2 * t ^ 2 := by field_simp
      _ < ε * t ^ 2 := by nlinarith
  have hsum := hrem.add hmain
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp
  ring

end Taylor

/-! ### Comparison of second derivatives -/

section Compare

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {f₁ : E₁ → ℝ} {f₂ : E₂ → ℝ} {p₁ : E₁} {p₂ : E₂}

/-- The line through a point. -/
theorem hasDerivAt_line (p v : E₁) : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
  have h0 := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  rwa [one_smul] at h0

/-- If f₂ ∘ R = f₁ near a common critical point, the second derivative of f₁ is the second
derivative of f₂ on the image of the derivative of R. -/
theorem sndDeriv_eq_of_comp {R : E₁ → E₂} {L : E₁ →L[ℝ] E₂} (hR0 : R p₁ = p₂)
    (hf₁ : ContDiffAt ℝ 2 f₁ p₁) (hf₂ : ContDiffAt ℝ 2 f₂ p₂) (h₁ : fderiv ℝ f₁ p₁ = 0)
    (h₂ : fderiv ℝ f₂ p₂ = 0) (hR : HasFDerivAt R L p₁)
    (hcomp : ∀ᶠ x in 𝓝 p₁, f₂ (R x) = f₁ x) (v : E₁) :
    fderiv ℝ (fderiv ℝ f₁) p₁ v v = fderiv ℝ (fderiv ℝ f₂) p₂ (L v) (L v) := by
  subst hR0
  have hl := hasDerivAt_line p₁ v
  have hl0 : (fun t : ℝ => p₁ + t • v) 0 = p₁ := by simp
  have hR' : HasFDerivAt R L ((fun t : ℝ => p₁ + t • v) 0) := by rw [hl0]; exact hR
  have hγ₂ : HasDerivAt (fun t : ℝ => R (p₁ + t • v)) (L v) 0 := hR'.comp_hasDerivAt 0 hl
  have T1 := tendsto_div_sq hf₁ h₁ hl hl0
  have T2 := tendsto_div_sq hf₂ h₂ hγ₂ (by simp)
  have ht : Tendsto (fun t : ℝ => p₁ + t • v) (𝓝[≠] 0) (𝓝 p₁) := by
    have h0 : Tendsto (fun t : ℝ => p₁ + t • v) (𝓝 0) (𝓝 (p₁ + (0 : ℝ) • v)) :=
      hl.continuousAt.tendsto
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have heq : (fun t : ℝ => (f₂ (R (p₁ + t • v)) - f₂ (R p₁)) / t ^ 2) =ᶠ[𝓝[≠] 0]
      fun t : ℝ => (f₁ (p₁ + t • v) - f₁ p₁) / t ^ 2 := by
    filter_upwards [ht.eventually hcomp] with t ht'
    rw [ht', hcomp.self_of_nhds]
  have h := tendsto_nhds_unique T1 (T2.congr' heq)
  linarith

/-- If f₁ ∘ ρ ≤ f₂ near a common critical point with equal values, the second derivative of f₁
on the image of the derivative of ρ is at most the second derivative of f₂. -/
theorem sndDeriv_le_of_le {ρ : E₂ → E₁} {π : E₂ →L[ℝ] E₁} (hρ0 : ρ p₂ = p₁)
    (hf₁ : ContDiffAt ℝ 2 f₁ p₁) (hf₂ : ContDiffAt ℝ 2 f₂ p₂) (h₁ : fderiv ℝ f₁ p₁ = 0)
    (h₂ : fderiv ℝ f₂ p₂ = 0) (hρ : HasFDerivAt ρ π p₂)
    (hle : ∀ᶠ y in 𝓝 p₂, f₁ (ρ y) ≤ f₂ y) (heq : f₁ p₁ = f₂ p₂) (u : E₂) :
    fderiv ℝ (fderiv ℝ f₁) p₁ (π u) (π u) ≤ fderiv ℝ (fderiv ℝ f₂) p₂ u u := by
  subst hρ0
  have hl := hasDerivAt_line p₂ u
  have hl0 : (fun t : ℝ => p₂ + t • u) 0 = p₂ := by simp
  have hρ' : HasFDerivAt ρ π ((fun t : ℝ => p₂ + t • u) 0) := by rw [hl0]; exact hρ
  have hγ₁ : HasDerivAt (fun t : ℝ => ρ (p₂ + t • u)) (π u) 0 := hρ'.comp_hasDerivAt 0 hl
  have T1 := tendsto_div_sq hf₁ h₁ hγ₁ (by simp)
  have T2 := tendsto_div_sq hf₂ h₂ hl hl0
  have ht : Tendsto (fun t : ℝ => p₂ + t • u) (𝓝[≠] 0) (𝓝 p₂) := by
    have h0 : Tendsto (fun t : ℝ => p₂ + t • u) (𝓝 0) (𝓝 (p₂ + (0 : ℝ) • u)) :=
      hl.continuousAt.tendsto
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hev : (fun t : ℝ => (f₁ (ρ (p₂ + t • u)) - f₁ (ρ p₂)) / t ^ 2) ≤ᶠ[𝓝[≠] 0]
      fun t : ℝ => (f₂ (p₂ + t • u) - f₂ p₂) / t ^ 2 := by
    filter_upwards [ht.eventually hle, self_mem_nhdsWithin] with t ht' ht0
    have ht2 : (0 : ℝ) < t ^ 2 := by
      have : t ≠ 0 := ht0
      positivity
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) ht2.le
  have h := le_of_tendsto_of_tendsto T1 T2 hev
  linarith

/-- If f₁ ∘ ρ ≤ f₂ near p₂ with equality at p₂ and ρ p₂ is critical for f₁, then p₂ is critical
for f₂. -/
theorem fderiv_eq_zero_of_le {ρ : E₂ → E₁} {π : E₂ →L[ℝ] E₁} (hρ0 : ρ p₂ = p₁)
    (hf₁ : DifferentiableAt ℝ f₁ p₁) (hf₂ : DifferentiableAt ℝ f₂ p₂)
    (h₁ : fderiv ℝ f₁ p₁ = 0) (hρ : HasFDerivAt ρ π p₂)
    (hle : ∀ᶠ y in 𝓝 p₂, f₁ (ρ y) ≤ f₂ y) (heq : f₁ p₁ = f₂ p₂) : fderiv ℝ f₂ p₂ = 0 := by
  subst hρ0
  have hmin : IsLocalMin (fun y => f₂ y - f₁ (ρ y)) p₂ := by
    filter_upwards [hle] with y hy
    rw [heq, sub_self]
    linarith
  have hd : HasFDerivAt (fun y => f₂ y - f₁ (ρ y))
      (fderiv ℝ f₂ p₂ - (fderiv ℝ f₁ (ρ p₂)).comp π) p₂ :=
    hf₂.hasFDerivAt.sub (hf₁.hasFDerivAt.comp p₂ hρ)
  have h0 := hmin.hasFDerivAt_eq_zero hd
  rw [h₁, ContinuousLinearMap.zero_comp, sub_zero] at h0
  exact h0

end Compare

/-! ### Comparison of the negative indices -/

section Index

variable {M M' : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  [AddCommGroup M'] [Module ℝ M'] [FiniteDimensional ℝ M']

/-- A linear map which does not increase the forms does not decrease the negative index of
inertia. -/
theorem sigNeg_le_of_le (Q : QuadraticForm ℝ M) (Q' : QuadraticForm ℝ M') (π : M →ₗ[ℝ] M')
    (h : ∀ u, Q' (π u) ≤ Q u) : sigNeg Q ≤ sigNeg Q' := by
  obtain ⟨U, hU, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  have hinj : Function.Injective (π.domRestrict U) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    by_contra hne
    have hpos := hneg u hne
    rw [restrict_apply, neg_apply] at hpos
    have hπ : π (u : M) = 0 := hu
    have h0 := h (u : M)
    rw [hπ, QuadraticMap.map_zero] at h0
    linarith
  have hrank : finrank ℝ (U.map π) = finrank ℝ U := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  rw [← hU, ← hrank]
  apply le_sigNeg_of_negDef Q' (V := U.map π)
  rintro ⟨_, ⟨u, hu, rfl⟩⟩ hne
  have hu0 : (⟨u, hu⟩ : U) ≠ 0 := fun h0 => hne (by
    have hu00 : u = 0 := congrArg Subtype.val h0
    apply Subtype.ext
    change π u = 0
    rw [hu00, map_zero])
  have hpos := hneg ⟨u, hu⟩ hu0
  rw [restrict_apply, neg_apply] at hpos
  rw [restrict_apply, neg_apply]
  have h0 := h u
  linarith

end Index

section Main

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {f₁ : E₁ → ℝ} {f₂ : E₂ → ℝ} {p₁ : E₁} {p₂ : E₂}

/-- **Equality of the indices under a section and a retraction.** If f₂ ∘ R = f₁ near p₁ and
f₁ ∘ ρ ≤ f₂ near p₂, with R p₁ = p₂, ρ p₂ = p₁ and p₁ critical for f₁, then the Hessians of f₁
at p₁ and of f₂ at p₂ have the same negative index of inertia. -/
theorem sigNeg_eq_of_retraction {R : E₁ → E₂} {ρ : E₂ → E₁} {L : E₁ →L[ℝ] E₂}
    {π : E₂ →L[ℝ] E₁} (hR0 : R p₁ = p₂) (hρ0 : ρ p₂ = p₁)
    (hf₁ : ContDiffAt ℝ 2 f₁ p₁) (hf₂ : ContDiffAt ℝ 2 f₂ p₂) (h₁ : fderiv ℝ f₁ p₁ = 0)
    (hR : HasFDerivAt R L p₁) (hρ : HasFDerivAt ρ π p₂)
    (hcomp : ∀ᶠ x in 𝓝 p₁, f₂ (R x) = f₁ x) (hle : ∀ᶠ y in 𝓝 p₂, f₁ (ρ y) ≤ f₂ y) :
    sigNeg (quad (Hessian.operator f₁ p₁)) = sigNeg (quad (Hessian.operator f₂ p₂)) := by
  have heq : f₁ p₁ = f₂ p₂ := by
    have h := hcomp.self_of_nhds
    rw [hR0] at h
    exact h.symm
  have h₂ : fderiv ℝ f₂ p₂ = 0 :=
    fderiv_eq_zero_of_le hρ0 (hf₁.differentiableAt (by simp)) (hf₂.differentiableAt (by simp))
      h₁ hρ hle heq
  have hq₁ : ∀ v, quad (Hessian.operator f₁ p₁) v = fderiv ℝ (fderiv ℝ f₁) p₁ v v := fun v => by
    rw [quad_apply, Hessian.inner_operator]
  have hq₂ : ∀ u, quad (Hessian.operator f₂ p₂) u = fderiv ℝ (fderiv ℝ f₂) p₂ u u := fun u => by
    rw [quad_apply, Hessian.inner_operator]
  refine le_antisymm ?_ ?_
  · refine sigNeg_le_of_le _ _ L.toLinearMap fun v => ?_
    change quad (Hessian.operator f₂ p₂) (L v) ≤ _
    rw [hq₁, hq₂, sndDeriv_eq_of_comp hR0 hf₁ hf₂ h₁ h₂ hR hcomp v]
  · refine sigNeg_le_of_le _ _ π.toLinearMap fun u => ?_
    change quad (Hessian.operator f₁ p₁) (π u) ≤ _
    rw [hq₁, hq₂]
    exact sndDeriv_le_of_le hρ0 hf₁ hf₂ h₁ h₂ hρ hle heq u

end Main

end

end Finsler.IndexComparison
