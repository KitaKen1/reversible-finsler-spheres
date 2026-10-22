module

public import Finsler.Geometry.LabelDeform

/-! The deformed penalized energy near a critical circle, on the ambient polygons. With the
coordinates cOf Q = (zOf Q, xiOf Q) of v0.116 put

  β(Q) = χ(cOf Q) (model(cOf Q) - Ψ(cOf Q)),   g'(Q) = pen(Q) + β(Q).

Where the frame coordinates are invertible, g' ∘ coord is the deformed function G of frame
coordinates near each point, so the derivative of g' in the direction of the ambient split field
is the derivative of G in the direction of the split field; g' is the model in coordinates where
the cutoff is 1, and the penalized energy where it is 0. If the closed support of χ₀ lies in a
compact set K₀ over which the frame coordinates are invertible and the penalized energy is C³
on the coefficients of norm at most R, and r² e^λ ≤ R², then β is differentiable everywhere, its
closed support lies in the image of the compact set tsupport χ₀ × {sqE ≤ r² e^λ}, and
|β| ≤ (C₁ + 1) r² e^λ when the fibre growth constant is C₁. -/

@[expose] public section

namespace Finsler.LabelAmbient

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LogCutoff Finsler.LabelDeform
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))

/-- The frame coordinates of an ambient polygon. -/
def cOf (Q : ZMod (m * N) → Ambient n) : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) :=
  (zOf m N Q, xiOf m N G₁ G₂ ψ Q)

/-- The deformation of the penalized energy near the circle. -/
def beta (χ₀ : (ZMod N → Ambient n) → ℝ) (r lam : ℝ) (Q : ZMod (m * N) → Ambient n) : ℝ :=
  cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q) *
    (model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q) - psi m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q))

/-- The deformed penalized energy. -/
def gDef (χ₀ : (ZMod N → Ambient n) → ℝ) (r lam : ℝ) (Q : ZMod (m * N) → Ambient n) : ℝ :=
  pen F (m * N) 1 Q + beta m N F G₁ G₂ ψ χ₀ r lam Q

variable {χ₀ : (ZMod N → Ambient n) → ℝ} {r lam : ℝ}

/-- The root polygons with invertible frame coordinates form an open set. -/
theorem isOpen_isUnit_root (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂) :
    IsOpen {z : ZMod N → Ambient n | IsUnit (matA m N G₁ G₂ ψ z)} := by
  have h := (isOpen_isUnit m N G₁ G₂ ψ hG₁ hG₂).preimage (iterA (n := n) m N).continuous
  have e : {z : ZMod N → Ambient n | IsUnit (matA m N G₁ G₂ ψ z)} =
      (iterA (n := n) m N) ⁻¹' {Q | IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))} := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage]
    have hz : zOf m N (iterA m N z) = z := by
      have h0 := zOf_iterA_add m N (z := z) (Submodule.zero_mem _)
      rwa [add_zero] at h0
    rw [hz]
  rw [e]
  exact h

/-- In frame coordinates the deformed penalized energy is the deformed function. -/
theorem gDef_coord {z : ZMod N → Ambient n} (hz : IsUnit (matA m N G₁ G₂ ψ z))
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    gDef m N F G₁ G₂ ψ χ₀ r lam (coord m N G₁ G₂ (z, ξ)) = deformG m N F G₁ G₂ χ₀ r lam (z, ξ) := by
  obtain ⟨h1, h2⟩ := inverse_coord m N G₁ G₂ ψ hz ξ
  have hc : cOf m N G₁ G₂ ψ (coord m N G₁ G₂ (z, ξ)) = (z, ξ) := Prod.ext h1 h2
  unfold gDef beta deformG
  rw [hc]
  rfl

theorem gDef_comp_coord_eventuallyEq (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {z : ZMod N → Ambient n} (hz : IsUnit (matA m N G₁ G₂ ψ z)) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    (gDef m N F G₁ G₂ ψ χ₀ r lam ∘ coord m N G₁ G₂) =ᶠ[𝓝 (z, ξ)]
      deformG m N F G₁ G₂ χ₀ r lam := by
  have hO : IsOpen (Prod.fst ⁻¹' {z : ZMod N → Ambient n | IsUnit (matA m N G₁ G₂ ψ z)} :
      Set ((ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)))) :=
    (isOpen_isUnit_root m N G₁ G₂ ψ hG₁ hG₂).preimage continuous_fst
  filter_upwards [hO.mem_nhds (show (z, ξ) ∈ Prod.fst ⁻¹' _ from hz)] with q hq
  exact gDef_coord m N F G₁ G₂ ψ hq q.2

/-- **The derivative along the ambient split field.** -/
theorem fderiv_gDef_splitW (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n) {Q : ZMod (m * N) → Ambient n}
    (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (hd : DifferentiableAt ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam) Q) :
    fderiv ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam) Q (splitW m N G₁ G₂ ψ V₀ Q) =
      fderiv ℝ (deformG m N F G₁ G₂ χ₀ r lam) (zOf m N Q, xiOf m N G₁ G₂ ψ Q)
        (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q)) := by
  have hc := coord_inverse m N G₁ G₂ ψ hQ
  have hcd : DifferentiableAt ℝ (coord m N G₁ G₂) (zOf m N Q, xiOf m N G₁ G₂ ψ Q) :=
    ((coord_contDiff m N G₁ G₂ hG₁ hG₂).differentiable (by simp)) _
  have hd' : DifferentiableAt ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam)
      (coord m N G₁ G₂ (zOf m N Q, xiOf m N G₁ G₂ ψ Q)) := by
    rw [hc]
    exact hd
  have h := (hd'.hasFDerivAt.comp (zOf m N Q, xiOf m N G₁ G₂ ψ Q) hcd.hasFDerivAt).fderiv
  have he := (gDef_comp_coord_eventuallyEq m N F G₁ G₂ ψ hG₁ hG₂ (χ₀ := χ₀) (r := r)
    (lam := lam) hQ (xiOf m N G₁ G₂ ψ Q)).fderiv_eq (𝕜 := ℝ)
  rw [he, hc] at h
  rw [h]
  rfl

/-- Where the cutoff is 1 the deformed penalized energy is the model in frame coordinates. -/
theorem gDef_of_cutoff_eq_one {Q : ZMod (m * N) → Ambient n}
    (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))) (h1 : cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q) = 1) :
    gDef m N F G₁ G₂ ψ χ₀ r lam Q = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q) := by
  have hc := coord_inverse m N G₁ G₂ ψ hQ
  have hpsi : psi m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q) = pen F (m * N) 1 Q := by
    change pen F (m * N) 1 (coord m N G₁ G₂ (zOf m N Q, xiOf m N G₁ G₂ ψ Q)) = _
    rw [hc]
  unfold gDef beta
  rw [h1, one_mul, hpsi]
  ring

/-- Where the cutoff is 0 the deformed penalized energy is the penalized energy. -/
theorem gDef_of_cutoff_eq_zero {Q : ZMod (m * N) → Ambient n}
    (h0 : cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q) = 0) :
    gDef m N F G₁ G₂ ψ χ₀ r lam Q = pen F (m * N) 1 Q := by
  unfold gDef beta
  rw [h0, zero_mul, add_zero]

/-- The deformation vanishes near a point whose cutoff vanishes nearby. -/
theorem beta_eventually_zero {Q : ZMod (m * N) → Ambient n}
    (h : ∀ᶠ Q' in 𝓝 Q, cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q') = 0) :
    beta m N F G₁ G₂ ψ χ₀ r lam =ᶠ[𝓝 Q] fun _ => 0 := by
  filter_upwards [h] with Q' hQ'
  unfold beta
  rw [hQ', zero_mul]

/-- **Differentiability of the deformation.** -/
theorem beta_differentiableAt (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K₀ : Set (ZMod N → Ambient n)} {R : ℝ} (hR : 0 ≤ R)
    (hest : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)))
    (hχ : ContDiff ℝ ∞ χ₀) (hsupp : tsupport χ₀ ⊆ K₀ ∩ {z | IsUnit (matA m N G₁ G₂ ψ z)})
    (hr : r ≠ 0) (hlam : 0 < lam) (hrR : r ^ 2 * Real.exp lam ≤ R ^ 2)
    (Q : ZMod (m * N) → Ambient n) :
    DifferentiableAt ℝ (beta m N F G₁ G₂ ψ χ₀ r lam) Q := by
  by_cases hz : zOf m N Q ∈ tsupport χ₀
  · obtain ⟨hzK, hzU⟩ := hsupp hz
    have hxi : ContDiffAt ℝ ∞ (xiOf m N G₁ G₂ ψ) Q := xiOf_contDiffAt m N G₁ G₂ ψ hG₁ hG₂ hzU
    have hcOf : DifferentiableAt ℝ (cOf m N G₁ G₂ ψ) Q :=
      ((zOf (n := n) m N).differentiableAt).prodMk (hxi.differentiableAt (by simp))
    by_cases hξ : ‖xiOf m N G₁ G₂ ψ Q‖ ≤ R
    · have hcoord := coord_contDiff m N G₁ G₂ hG₁ hG₂
      have hpsi : DifferentiableAt ℝ (psi m N F G₁ G₂) (cOf m N G₁ G₂ ψ Q) :=
        (ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) _ (hest _ hzK _ hξ)
          (hcoord.contDiffAt.of_le (by simp))).differentiableAt (by norm_num)
      have hpsi0 : DifferentiableAt ℝ (psi m N F G₁ G₂) (zOf m N Q, 0) :=
        (ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) _
          (hest _ hzK 0 (by rw [norm_zero]; exact hR))
          (hcoord.contDiffAt.of_le (by simp))).differentiableAt (by norm_num)
      have hmodel : DifferentiableAt ℝ (model m N F G₁ G₂) (cOf m N G₁ G₂ ψ Q) := by
        have h1 : DifferentiableAt ℝ
            (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
              psi m N F G₁ G₂ (q.1, 0)) (cOf m N G₁ G₂ ψ Q) := by
          have hL : DifferentiableAt ℝ
              (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
                ((q.1, 0) : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))))
              (cOf m N G₁ G₂ ψ Q) := differentiableAt_fst.prodMk (differentiableAt_const _)
          exact DifferentiableAt.comp (cOf m N G₁ G₂ ψ Q) (g := psi m N F G₁ G₂) hpsi0 hL
        have h2 : DifferentiableAt ℝ
            (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) => sqX q.2)
            (cOf m N G₁ G₂ ψ Q) :=
          (sqX_contDiff.differentiable (by simp) _).comp _ differentiableAt_snd
        have h3 : DifferentiableAt ℝ
            (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) => sqY q.2)
            (cOf m N G₁ G₂ ψ Q) :=
          (sqY_contDiff.differentiable (by simp) _).comp _ differentiableAt_snd
        exact (h1.sub h2).add h3
      have hcut : DifferentiableAt ℝ (cutoff (b := b) (p := p) χ₀ r lam) (cOf m N G₁ G₂ ψ Q) :=
        (cutoff_contDiff hr hlam hχ).differentiable (by simp) _
      exact (hcut.comp Q hcOf).mul ((hmodel.comp Q hcOf).sub (hpsi.comp Q hcOf))
    · rw [not_le] at hξ
      have hlt : r ^ 2 * Real.exp lam < sqE (xiOf m N G₁ G₂ ψ Q) := by
        have h1 : R ^ 2 < ‖xiOf m N G₁ G₂ ψ Q‖ ^ 2 := pow_lt_pow_left₀ hξ hR two_ne_zero
        exact lt_of_le_of_lt hrR (lt_of_lt_of_le h1 (sq_norm_le_sqE _))
      have hcont : ContinuousAt (fun Q' => sqE (xiOf m N G₁ G₂ ψ Q')) Q :=
        sqE_contDiff.continuous.continuousAt.comp hxi.continuousAt
      have hev : ∀ᶠ Q' in 𝓝 Q, cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q') = 0 := by
        filter_upwards [hcont.eventually (lt_mem_nhds hlt)] with Q' hQ'
        exact cutoff_eq_zero_of_ge hr hlam hQ'.le
      exact ((differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
        (beta_eventually_zero m N F G₁ G₂ ψ hev))
  · have hO : IsOpen {Q' : ZMod (m * N) → Ambient n | zOf m N Q' ∉ tsupport χ₀} :=
      (isClosed_tsupport χ₀).isOpen_compl.preimage (zOf (n := n) m N).continuous
    have hev : ∀ᶠ Q' in 𝓝 Q, cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q') = 0 := by
      filter_upwards [hO.mem_nhds hz] with Q' hQ'
      exact cutoff_eq_zero_of_base (image_eq_zero_of_notMem_tsupport hQ')
    exact ((differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
      (beta_eventually_zero m N F G₁ G₂ ψ hev))

/-- At a point where the cutoff does not vanish, the root polygon lies in the closed support of
χ₀ and sqE of the coefficients is below r² e^λ. -/
theorem mem_of_cutoff_ne_zero (hr : r ≠ 0) (hlam : 0 < lam) {Q : ZMod (m * N) → Ambient n}
    (h : cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q) ≠ 0) :
    zOf m N Q ∈ tsupport χ₀ ∧ sqE (xiOf m N G₁ G₂ ψ Q) < r ^ 2 * Real.exp lam := by
  refine ⟨subset_tsupport χ₀ fun h0 => h (cutoff_eq_zero_of_base h0), ?_⟩
  by_contra hge
  rw [not_lt] at hge
  exact h (cutoff_eq_zero_of_ge hr hlam hge)

/-- **The size of the deformation.** -/
theorem abs_beta_le {K₀ : Set (ZMod N → Ambient n)} {R C₁ : ℝ} (hR : 0 ≤ R)
    (hquad : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| ≤ C₁ * ‖ξ‖ ^ 2)
    (hC₁ : 0 ≤ C₁) (hsupp : tsupport χ₀ ⊆ K₀) (hχ0 : ∀ z, 0 ≤ χ₀ z) (hχ1 : ∀ z, χ₀ z ≤ 1)
    (hr : r ≠ 0) (hlam : 0 < lam) (hrR : r ^ 2 * Real.exp lam ≤ R ^ 2)
    (Q : ZMod (m * N) → Ambient n) :
    |beta m N F G₁ G₂ ψ χ₀ r lam Q| ≤ (C₁ + 1) * (r ^ 2 * Real.exp lam) := by
  have hpos : 0 ≤ (C₁ + 1) * (r ^ 2 * Real.exp lam) := by positivity
  by_cases h0 : cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q) = 0
  · unfold beta
    rw [h0, zero_mul, abs_zero]
    exact hpos
  · obtain ⟨hz, hξ⟩ := mem_of_cutoff_ne_zero m N G₁ G₂ ψ hr hlam h0
    have hξR : ‖xiOf m N G₁ G₂ ψ Q‖ ≤ R := by
      have h1 : ‖xiOf m N G₁ G₂ ψ Q‖ ^ 2 ≤ R ^ 2 :=
        ((sq_norm_le_sqE _).trans hξ.le).trans hrR
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp h1
    have hδ := abs_model_sub_psi_le m N F G₁ G₂ hquad hC₁ (hsupp hz) hξR
    have hc0 := cutoff_nonneg hχ0 (r := r) (lam := lam) (cOf m N G₁ G₂ ψ Q)
    have hc1 := cutoff_le_one hχ1 (r := r) (lam := lam) (cOf m N G₁ G₂ ψ Q)
    unfold beta
    rw [abs_mul, abs_of_nonneg hc0]
    calc cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q) *
          |model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q) - psi m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q)|
        ≤ 1 * ((C₁ + 1) * sqE (xiOf m N G₁ G₂ ψ Q)) :=
          mul_le_mul hc1 hδ (abs_nonneg _) zero_le_one
      _ ≤ (C₁ + 1) * (r ^ 2 * Real.exp lam) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hξ.le (by linarith)

/-- **The support of the deformation.** It lies in the image under the frame coordinates of the
compact set tsupport χ₀ × {sqE ≤ r² e^λ}. -/
theorem tsupport_beta_subset (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K₀ : Set (ZMod N → Ambient n)} (hK : IsCompact K₀)
    (hsupp : tsupport χ₀ ⊆ K₀ ∩ {z | IsUnit (matA m N G₁ G₂ ψ z)}) (hr : r ≠ 0) (hlam : 0 < lam) :
    IsCompact (coord m N G₁ G₂ '' (tsupport χ₀ ×ˢ {ξ | sqE ξ ≤ r ^ 2 * Real.exp lam})) ∧
      tsupport (beta m N F G₁ G₂ ψ χ₀ r lam) ⊆
        coord m N G₁ G₂ '' (tsupport χ₀ ×ˢ {ξ | sqE ξ ≤ r ^ 2 * Real.exp lam}) := by
  have hT : IsCompact (tsupport χ₀) :=
    hK.of_isClosed_subset (isClosed_tsupport χ₀) fun z hz => (hsupp hz).1
  have hS : IsCompact {ξ : (Fin b → ℝ) × (Fin p → ℝ) | sqE ξ ≤ r ^ 2 * Real.exp lam} := by
    have hcl : IsClosed {ξ : (Fin b → ℝ) × (Fin p → ℝ) | sqE ξ ≤ r ^ 2 * Real.exp lam} :=
      isClosed_le sqE_contDiff.continuous continuous_const
    refine (isCompact_closedBall (0 : (Fin b → ℝ) × (Fin p → ℝ))
      (Real.sqrt (r ^ 2 * Real.exp lam))).of_isClosed_subset hcl fun ξ hξ => ?_
    rw [mem_closedBall_zero_iff]
    exact Real.le_sqrt_of_sq_le ((sq_norm_le_sqE ξ).trans hξ)
  have hC : IsCompact (coord m N G₁ G₂ '' (tsupport χ₀ ×ˢ
      {ξ | sqE ξ ≤ r ^ 2 * Real.exp lam})) :=
    (hT.prod hS).image (coord_contDiff m N G₁ G₂ hG₁ hG₂).continuous
  refine ⟨hC, closure_minimal ?_ hC.isClosed⟩
  intro Q hQ
  have h0 : cutoff χ₀ r lam (cOf m N G₁ G₂ ψ Q) ≠ 0 := by
    intro h0
    apply hQ
    unfold beta
    rw [h0, zero_mul]
  obtain ⟨hz, hξ⟩ := mem_of_cutoff_ne_zero m N G₁ G₂ ψ hr hlam h0
  refine ⟨cOf m N G₁ G₂ ψ Q, ⟨hz, hξ.le⟩, ?_⟩
  exact coord_inverse m N G₁ G₂ ψ (hsupp hz).2

/-- **Descent of the deformed penalized energy along the ambient split field.** -/
theorem gDef_splitW_le (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)
    {K₀ : Set (ZMod N → Ambient n)} {R κ c C₁ : ℝ}
    (hest : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2)
    (hquad : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| ≤ C₁ * ‖ξ‖ ^ 2)
    (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hχ : ContDiff ℝ ∞ χ₀) (hχ0 : ∀ z, 0 ≤ χ₀ z) (hχ1 : ∀ z, χ₀ z ≤ 1) {B : ℝ}
    (hB : ∀ z, ‖fderiv ℝ χ₀ z‖ ≤ B) {M : ℝ} (hr : r ≠ 0) (hlam : 0 < lam)
    (hM : ∀ x, |deriv Real.smoothTransition x| ≤ M)
    (hsmall : (C₁ + 1) * (B * κ + 2 * M / lam) ≤ min (c / (b + p + 1)) 2 / 2)
    {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (hzK : zOf m N Q ∈ K₀) (hξ : ‖xiOf m N G₁ G₂ ψ Q‖ ≤ R) (hv : ‖V₀ (zOf m N Q)‖ ≤ κ)
    (hd : DifferentiableAt ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam) Q) :
    fderiv ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam) Q (splitW m N G₁ G₂ ψ V₀ Q) ≤
      (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) (zOf m N Q) (V₀ (zOf m N Q)) -
        min (c / (b + p + 1)) 2 / 2 * sqE (xiOf m N G₁ G₂ ψ Q) := by
  rw [fderiv_gDef_splitW m N F G₁ G₂ ψ hG₁ hG₂ V₀ hQ hd]
  have h := deformG_descent m N F G₁ G₂ hG₁ hG₂ hest hquad hc hC₁ hχ hχ0 hχ1 hB hr hlam hM
    hsmall hzK hξ hv
  have hR : 0 ≤ R := (norm_nonneg _).trans hξ
  have hd0 : DifferentiableAt ℝ (psi m N F G₁ G₂) (zOf m N Q, 0) :=
    (ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) _
      (hest _ hzK 0 (by rw [norm_zero]; exact hR)).1
      ((coord_contDiff m N G₁ G₂ hG₁ hG₂).contDiffAt.of_le (by simp))).differentiableAt
      (by norm_num)
  rw [fderiv_psi_base m N F G₁ G₂ hd0] at h
  exact h

end

end Finsler.LabelAmbient
