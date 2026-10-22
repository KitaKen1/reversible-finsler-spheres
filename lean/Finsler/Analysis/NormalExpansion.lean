module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening

/-! Expansion of a function along the fibres of a product near a compact set of the zero
section. Let Ψ be a function on an open set 𝒪 of a product E₀ × X of normed spaces, X finite
dimensional, K₀ a compact subset of E₀ with K₀ × {0} ⊂ 𝒪, and suppose that the fibre derivative
of Ψ vanishes on the zero section. If Ψ is C², the fibre derivative at (z, x) is the second
fibre derivative at (z, 0) applied to x, up to an error ε ‖x‖ for small x, uniformly for z in
K₀. If Ψ is C³, the base derivative at (z, x) differs from the base derivative at (z, 0) by at
most a constant times ‖x‖², uniformly for z in K₀: the mixed second derivative vanishes on the
zero section by the symmetry of the second derivative. Consequently, if J is a linear map of X
with D²Ψ(z, 0)((0, x), (0, J x)) ≤ −2c ‖x‖² on K₀, then for small x and small base vectors v

  DΨ(z, x)(v, J x) ≤ DΨ(z, 0)(v, 0) − c ‖x‖².

This is the estimate which makes a field (v(z), J x) a descent direction near the zero section
whenever its base part is a descent direction of the restriction to the zero section. -/

@[expose] public section

namespace Finsler.NormalExpansion

open Set Metric Topology

noncomputable section
set_option maxSynthPendingDepth 3

variable {E₀ X : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup X]
  [NormedSpace ℝ X]

omit [NormedSpace ℝ E₀] [NormedSpace ℝ X] in
/-- A tube around a compact set of the zero section inside an open set. -/
theorem exists_tube {𝒪 : Set (E₀ × X)} (h𝒪 : IsOpen 𝒪) {K₀ : Set E₀} (hK : IsCompact K₀)
    (hsub : ∀ z ∈ K₀, (z, (0 : X)) ∈ 𝒪) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K₀, ∀ x : X, ‖x‖ ≤ R → (z, x) ∈ 𝒪 := by
  have hKc : IsCompact ((fun z : E₀ => (z, (0 : X))) '' K₀) :=
    hK.image (continuous_id.prodMk continuous_const)
  have hKsub : (fun z : E₀ => (z, (0 : X))) '' K₀ ⊆ 𝒪 := by
    rintro _ ⟨z, hz, rfl⟩
    exact hsub z hz
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open h𝒪 hKsub
  refine ⟨δ / 2, half_pos hδ, fun z hz x hx => hthick ?_⟩
  rw [mem_thickening_iff]
  refine ⟨(z, 0), ⟨z, hz, rfl⟩, ?_⟩
  rw [Prod.dist_eq, dist_self, dist_zero_right]
  exact max_lt hδ (lt_of_le_of_lt hx (half_lt_self hδ))

omit [NormedSpace ℝ E₀] [NormedSpace ℝ X] in
theorem norm_zero_prod (x : X) : ‖((0 : E₀), x)‖ = ‖x‖ := by
  rw [Prod.norm_def, norm_zero]
  exact max_eq_right (norm_nonneg x)

omit [NormedSpace ℝ E₀] [NormedSpace ℝ X] in
theorem norm_prod_zero (v : E₀) : ‖(v, (0 : X))‖ = ‖v‖ := by
  rw [Prod.norm_def, norm_zero]
  exact max_eq_left (norm_nonneg v)

/-- The derivative of a function along a fibre segment. -/
theorem hasDerivAt_segment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E₀ × X → F} {g' : E₀ × X →L[ℝ] F} (z : E₀) (x : X) (t : ℝ)
    (hg : HasFDerivAt g g' (z, t • x)) :
    HasDerivAt (fun s : ℝ => g (z, s • x)) (g' (0, x)) t := by
  have hγ : HasDerivAt (fun s : ℝ => (z, s • x)) ((0 : E₀), x) t := by
    have h2 : HasDerivAt (fun s : ℝ => s • x) ((1 : ℝ) • x) t := (hasDerivAt_id t).smul_const x
    rw [one_smul] at h2
    exact (hasDerivAt_const t z).prodMk h2
  exact hg.comp_hasDerivAt t hγ

variable [FiniteDimensional ℝ X]

/-- The fibre derivative near the zero section is the second fibre derivative at the zero
section, up to a small multiple of the distance. -/
theorem exists_fibre_expansion {Ψ : E₀ × X → ℝ} {𝒪 : Set (E₀ × X)} (h𝒪 : IsOpen 𝒪)
    (hΨ : ContDiffOn ℝ 2 Ψ 𝒪) {K₀ : Set E₀} (hK : IsCompact K₀)
    (hsub : ∀ z ∈ K₀, (z, (0 : X)) ∈ 𝒪)
    (hcrit : ∀ z ∈ K₀, ∀ w : X, fderiv ℝ Ψ (z, 0) (0, w) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K₀, ∀ x : X, ‖x‖ ≤ R → (z, x) ∈ 𝒪 ∧ ∀ w : X,
      |fderiv ℝ Ψ (z, x) (0, w) - fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, x) (0, w)| ≤
        ε * ‖x‖ * ‖w‖ := by
  obtain ⟨R₀, hR₀, htube⟩ := exists_tube h𝒪 hK hsub
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ Ψ) 𝒪 := hΨ.fderiv_of_isOpen h𝒪 (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ Ψ)) 𝒪 :=
    (h1.fderiv_of_isOpen h𝒪 (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  have hT : IsCompact (K₀ ×ˢ closedBall (0 : X) R₀) := hK.prod (isCompact_closedBall 0 R₀)
  have hTsub : K₀ ×ˢ closedBall (0 : X) R₀ ⊆ 𝒪 := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    exact htube z hz x (mem_closedBall_zero_iff.mp hx)
  have huc := hT.uniformContinuousOn_of_continuous (h2.mono hTsub)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨min R₀ (δ / 2), lt_min hR₀ (half_pos hδ), fun z hz x hx => ?_⟩
  have hxR₀ : ‖x‖ ≤ R₀ := hx.trans (min_le_left _ _)
  have hxδ : ‖x‖ < δ := lt_of_le_of_lt (hx.trans (min_le_right _ _)) (half_lt_self hδ)
  refine ⟨htube z hz x hxR₀, fun w => ?_⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (z, t • x) ∈ K₀ ×ˢ closedBall (0 : X) R₀ := by
    intro t ht
    refine ⟨hz, mem_closedBall_zero_iff.mpr ?_⟩
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans hxR₀
  have hF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) (z, t • x)) (z, t • x) := fun t ht =>
    (((h1.differentiableOn one_ne_zero) _ (hTsub (hseg t ht))).differentiableAt
      (h𝒪.mem_nhds (hTsub (hseg t ht)))).hasFDerivAt
  set A : ℝ := fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, x) (0, w) with hA
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => fderiv ℝ Ψ (z, s • x) (0, w) - s * A)
      (fderiv ℝ (fderiv ℝ Ψ) (z, t • x) (0, x) (0, w) - A) (Icc 0 1) t := by
    intro t ht
    have h3 := hasDerivAt_segment z x t (hF t ht)
    have h4 : HasDerivAt (fun s : ℝ => fderiv ℝ Ψ (z, s • x) (0, w))
        (fderiv ℝ (fderiv ℝ Ψ) (z, t • x) (0, x) (0, w)) t :=
      (ContinuousLinearMap.apply ℝ ℝ ((0 : E₀), w)).hasFDerivAt.comp_hasDerivAt t h3
    have h5 : HasDerivAt (fun s : ℝ => s * A) A t := by
      simpa using (hasDerivAt_id t).mul_const A
    exact (h4.sub h5).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ Ψ) (z, t • x) (0, x) (0, w) - A‖ ≤ ε * ‖x‖ * ‖w‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have h0 : (z, (0 : X)) ∈ K₀ ×ˢ closedBall (0 : X) R₀ :=
      ⟨hz, mem_closedBall_self hR₀.le⟩
    have hd : dist ((z, t • x) : E₀ × X) (z, 0) < δ := by
      rw [Prod.dist_eq, dist_self, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact max_lt hδ (lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg x) ht.2.le) hxδ)
    have h6 := hδ' _ (hseg t ht') _ h0 hd
    rw [dist_eq_norm] at h6
    have h7 : fderiv ℝ (fderiv ℝ Ψ) (z, t • x) (0, x) (0, w) - A =
        (fderiv ℝ (fderiv ℝ Ψ) (z, t • x) - fderiv ℝ (fderiv ℝ Ψ) (z, 0)) (0, x) (0, w) := by
      rw [hA]
      rfl
    rw [h7]
    calc ‖(fderiv ℝ (fderiv ℝ Ψ) (z, t • x) - fderiv ℝ (fderiv ℝ Ψ) (z, 0)) (0, x) (0, w)‖
        ≤ ‖(fderiv ℝ (fderiv ℝ Ψ) (z, t • x) - fderiv ℝ (fderiv ℝ Ψ) (z, 0)) (0, x)‖ *
            ‖((0 : E₀), w)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ Ψ) (z, t • x) - fderiv ℝ (fderiv ℝ Ψ) (z, 0)‖ *
            ‖((0 : E₀), x)‖) * ‖((0 : E₀), w)‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (ε * ‖x‖) * ‖w‖ := by
          rw [norm_zero_prod, norm_zero_prod]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h6.le (norm_nonneg x)) (norm_nonneg w)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hbound
  have h8 : (fderiv ℝ Ψ (z, (1 : ℝ) • x) (0, w) - 1 * A) -
      (fderiv ℝ Ψ (z, (0 : ℝ) • x) (0, w) - 0 * A) =
      fderiv ℝ Ψ (z, x) (0, w) - A := by
    rw [one_smul, zero_smul, hcrit z hz w]
    ring
  rw [h8, Real.norm_eq_abs] at hmv
  exact hmv

/-- The base derivative near the zero section differs from the base derivative at the zero
section by at most a constant times the square of the distance. -/
theorem exists_base_expansion {Ψ : E₀ × X → ℝ} {𝒪 : Set (E₀ × X)} (h𝒪 : IsOpen 𝒪)
    (hΨ : ContDiffOn ℝ 3 Ψ 𝒪) {K₀ : Set E₀} (hK : IsCompact K₀)
    (hsub : ∀ z ∈ K₀, (z, (0 : X)) ∈ 𝒪)
    (hcrit : ∀ z : E₀, (z, (0 : X)) ∈ 𝒪 → ∀ w : X, fderiv ℝ Ψ (z, 0) (0, w) = 0) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ z ∈ K₀, ∀ x : X, ‖x‖ ≤ R → ∀ v : E₀,
      |fderiv ℝ Ψ (z, x) (v, 0) - fderiv ℝ Ψ (z, 0) (v, 0)| ≤ C * ‖x‖ ^ 2 * ‖v‖ := by
  obtain ⟨R₀, hR₀, htube⟩ := exists_tube h𝒪 hK hsub
  have h1 : ContDiffOn ℝ 2 (fderiv ℝ Ψ) 𝒪 := hΨ.fderiv_of_isOpen h𝒪 (by norm_num)
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ Ψ)) 𝒪 := h1.fderiv_of_isOpen h𝒪 (by norm_num)
  have h3 : ContinuousOn (fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ))) 𝒪 :=
    (h2.fderiv_of_isOpen h𝒪 (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  have hT : IsCompact (K₀ ×ˢ closedBall (0 : X) R₀) := hK.prod (isCompact_closedBall 0 R₀)
  have hTsub : K₀ ×ˢ closedBall (0 : X) R₀ ⊆ 𝒪 := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    exact htube z hz x (mem_closedBall_zero_iff.mp hx)
  obtain ⟨C₁, hC₁⟩ := hT.exists_bound_of_continuousOn (h3.mono hTsub)
  set C : ℝ := max C₁ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ p ∈ K₀ ×ˢ closedBall (0 : X) R₀,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) p‖ ≤ C := fun p hp => (hC₁ p hp).trans (le_max_left _ _)
  refine ⟨R₀, C, hR₀, hC0, fun z hz x hx v => ?_⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (z, t • x) ∈ K₀ ×ˢ closedBall (0 : X) R₀ := by
    intro t ht
    refine ⟨hz, mem_closedBall_zero_iff.mpr ?_⟩
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans hx
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (z, t • x) ∈ 𝒪 := fun t ht => hTsub (hseg t ht)
  have hF1 : ∀ p ∈ 𝒪, HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) p) p := fun p hp =>
    (((h1.differentiableOn (by norm_num)) p hp).differentiableAt (h𝒪.mem_nhds hp)).hasFDerivAt
  have hF2 : ∀ p ∈ 𝒪, HasFDerivAt (fderiv ℝ (fderiv ℝ Ψ))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) p) p := fun p hp =>
    (((h2.differentiableOn one_ne_zero) p hp).differentiableAt (h𝒪.mem_nhds hp)).hasFDerivAt
  -- the mixed second derivative vanishes on the zero section
  have hz0 : (z, (0 : X)) ∈ 𝒪 := hsub z hz
  have hmixed : fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, x) (v, 0) = 0 := by
    have hsymm : fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, x) (v, 0) =
        fderiv ℝ (fderiv ℝ Ψ) (z, 0) (v, 0) (0, x) :=
      ((hΨ.contDiffAt (h𝒪.mem_nhds hz0)).isSymmSndFDerivAt
        (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq _ _
    rw [hsymm]
    have hγ : HasDerivAt (fun σ : ℝ => (z + σ • v, (0 : X))) (v, (0 : X)) 0 := by
      have ha : HasDerivAt (fun σ : ℝ => z + σ • v) ((1 : ℝ) • v) 0 :=
        ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
      rw [one_smul] at ha
      exact ha.prodMk (hasDerivAt_const 0 (0 : X))
    have hcomp : HasDerivAt (fun σ : ℝ => fderiv ℝ Ψ (z + σ • v, 0))
        (fderiv ℝ (fderiv ℝ Ψ) (z, 0) (v, 0)) 0 := by
      have h : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) (z, 0))
          (z + (0 : ℝ) • v, (0 : X)) := by
        rw [zero_smul, add_zero]
        exact hF1 (z, 0) hz0
      exact h.comp_hasDerivAt (0 : ℝ) hγ
    have hev : HasDerivAt (fun σ : ℝ => fderiv ℝ Ψ (z + σ • v, 0) (0, x))
        (fderiv ℝ (fderiv ℝ Ψ) (z, 0) (v, 0) (0, x)) 0 :=
      (ContinuousLinearMap.apply ℝ ℝ ((0 : E₀), x)).hasFDerivAt.comp_hasDerivAt 0 hcomp
    have hzero : (fun σ : ℝ => fderiv ℝ Ψ (z + σ • v, 0) (0, x)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      have hcont : Continuous fun σ : ℝ => (z + σ • v, (0 : X)) := by fun_prop
      have hopen : ∀ᶠ σ : ℝ in 𝓝 0, (z + σ • v, (0 : X)) ∈ 𝒪 :=
        hcont.continuousAt.eventually (h𝒪.mem_nhds (by simpa using hz0))
      filter_upwards [hopen] with σ hσ
      exact hcrit _ hσ x
    exact hev.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero)
  -- the first derivative of the base derivative along the segment
  have hk : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => fderiv ℝ (fderiv ℝ Ψ) (z, s • x) (0, x) (v, 0))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) (z, t • x) (0, x) (0, x) (v, 0)) (Icc 0 1) t := by
    intro t ht
    have h4 := hasDerivAt_segment z x t (hF2 _ (hmem t ht))
    have h5 : HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ Ψ) (z, s • x) (0, x))
        (fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) (z, t • x) (0, x) (0, x)) t :=
      (ContinuousLinearMap.apply ℝ (E₀ × X →L[ℝ] ℝ) ((0 : E₀), x)).hasFDerivAt.comp_hasDerivAt
        t h4
    exact ((ContinuousLinearMap.apply ℝ ℝ (v, (0 : X))).hasFDerivAt.comp_hasDerivAt
      t h5).hasDerivWithinAt
  have hkb : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) (z, t • x) (0, x) (0, x) (v, 0)‖ ≤
        C * ‖x‖ ^ 2 * ‖v‖ := by
    intro t ht
    have h6 := hC _ (hseg t ⟨ht.1, ht.2.le⟩)
    calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) (z, t • x) (0, x) (0, x) (v, 0)‖
        ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) (z, t • x) (0, x) (0, x)‖ * ‖(v, (0 : X))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) (z, t • x) (0, x)‖ * ‖((0 : E₀), x)‖) *
            ‖(v, (0 : X))‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ((‖fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) (z, t • x)‖ * ‖((0 : E₀), x)‖) *
            ‖((0 : E₀), x)‖) * ‖(v, (0 : X))‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ((C * ‖x‖) * ‖x‖) * ‖v‖ := by
          rw [norm_zero_prod, norm_prod_zero]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h6 (norm_nonneg x)) (norm_nonneg x)) (norm_nonneg v)
      _ = C * ‖x‖ ^ 2 * ‖v‖ := by ring
  have hksmall : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ Ψ) (z, t • x) (0, x) (v, 0)‖ ≤ C * ‖x‖ ^ 2 * ‖v‖ := by
    intro t ht
    have h7 := norm_image_sub_le_of_norm_deriv_le_segment' hk hkb t ht
    rw [zero_smul, hmixed, sub_zero, sub_zero] at h7
    refine h7.trans ?_
    have hnn : 0 ≤ C * ‖x‖ ^ 2 * ‖v‖ := by positivity
    exact mul_le_of_le_one_right hnn ht.2
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => fderiv ℝ Ψ (z, s • x) (v, 0))
      (fderiv ℝ (fderiv ℝ Ψ) (z, t • x) (0, x) (v, 0)) (Icc 0 1) t := by
    intro t ht
    have h4 := hasDerivAt_segment z x t (hF1 _ (hmem t ht))
    exact ((ContinuousLinearMap.apply ℝ ℝ (v, (0 : X))).hasFDerivAt.comp_hasDerivAt
      t h4).hasDerivWithinAt
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hg
    (fun t ht => hksmall t ⟨ht.1, ht.2.le⟩)
  rw [one_smul, zero_smul, Real.norm_eq_abs] at hmv
  exact hmv

/-- The descent estimate for a field which is a given linear map on the fibres: if the second
fibre derivative at the zero section satisfies D²Ψ((0, x), (0, J x)) ≤ −2c ‖x‖² on a compact
set, then near it DΨ(z, x)(v, J x) ≤ DΨ(z, 0)(v, 0) − c ‖x‖² for small base vectors v. -/
theorem exists_split_descent {Ψ : E₀ × X → ℝ} {𝒪 : Set (E₀ × X)} (h𝒪 : IsOpen 𝒪)
    (hΨ : ContDiffOn ℝ 3 Ψ 𝒪) {K₀ : Set E₀} (hK : IsCompact K₀)
    (hsub : ∀ z ∈ K₀, (z, (0 : X)) ∈ 𝒪)
    (hcrit : ∀ z : E₀, (z, (0 : X)) ∈ 𝒪 → ∀ w : X, fderiv ℝ Ψ (z, 0) (0, w) = 0)
    (J : X →L[ℝ] X) {c : ℝ} (hc : 0 < c)
    (hJ : ∀ z ∈ K₀, ∀ x : X,
      fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, x) (0, J x) ≤ -(2 * c) * ‖x‖ ^ 2) :
    ∃ R κ : ℝ, 0 < R ∧ 0 < κ ∧ ∀ z ∈ K₀, ∀ x : X, ‖x‖ ≤ R → (z, x) ∈ 𝒪 ∧
      ∀ v : E₀, ‖v‖ ≤ κ →
        fderiv ℝ Ψ (z, x) (v, J x) ≤ fderiv ℝ Ψ (z, 0) (v, 0) - c * ‖x‖ ^ 2 := by
  have hε : 0 < c / (2 * (‖J‖ + 1)) := by positivity
  obtain ⟨R₁, hR₁, h1⟩ := exists_fibre_expansion h𝒪 (hΨ.of_le (by norm_num)) hK hsub
    (fun z hz w => hcrit z (hsub z hz) w) hε
  obtain ⟨R₂, C, hR₂, hC, h2⟩ := exists_base_expansion h𝒪 hΨ hK hsub hcrit
  refine ⟨min R₁ R₂, c / (2 * (C + 1)), lt_min hR₁ hR₂, by positivity, fun z hz x hx => ?_⟩
  obtain ⟨hmem, hfib⟩ := h1 z hz x (hx.trans (min_le_left _ _))
  refine ⟨hmem, fun v hv => ?_⟩
  have hsplit : fderiv ℝ Ψ (z, x) (v, J x) =
      fderiv ℝ Ψ (z, x) (v, 0) + fderiv ℝ Ψ (z, x) (0, J x) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hf := (abs_le.mp (hfib (J x))).2
  have hb := (abs_le.mp (h2 z hz x (hx.trans (min_le_right _ _)) v)).2
  have hJx : ‖J x‖ ≤ ‖J‖ * ‖x‖ := J.le_opNorm x
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have e1 : c / (2 * (‖J‖ + 1)) * ‖x‖ * ‖J x‖ ≤ c / 2 * ‖x‖ ^ 2 := by
    have h3 : c / (2 * (‖J‖ + 1)) * ‖x‖ * ‖J x‖ ≤ c / (2 * (‖J‖ + 1)) * ‖x‖ * (‖J‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left hJx (by positivity)
    have h4 : c / (2 * (‖J‖ + 1)) * ‖x‖ * (‖J‖ * ‖x‖) =
        c / 2 * ‖x‖ ^ 2 * (‖J‖ / (‖J‖ + 1)) := by
      field_simp
    have h5 : ‖J‖ / (‖J‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    rw [h4] at h3
    exact h3.trans (mul_le_of_le_one_right (by positivity) h5)
  have e2 : C * ‖x‖ ^ 2 * ‖v‖ ≤ c / 2 * ‖x‖ ^ 2 := by
    have h3 : C * ‖x‖ ^ 2 * ‖v‖ ≤ C * ‖x‖ ^ 2 * (c / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    have h4 : C * ‖x‖ ^ 2 * (c / (2 * (C + 1))) = c / 2 * ‖x‖ ^ 2 * (C / (C + 1)) := by
      field_simp
    have h5 : C / (C + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    rw [h4] at h3
    exact h3.trans (mul_le_of_le_one_right (by positivity) h5)
  have hJz := hJ z hz x
  rw [hsplit]
  linarith

end

end Finsler.NormalExpansion
