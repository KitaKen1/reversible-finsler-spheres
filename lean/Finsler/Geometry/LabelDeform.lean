module

public import Finsler.Geometry.LabelRegion
public import Finsler.Analysis.LogCutoff
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The deformed function near a critical circle, in frame coordinates. On the coefficients
ξ = (x, y) put sqX ξ = |x|², sqY ξ = |y|² and sqE = sqX + sqY with the Euclidean norms; then
|ξ|² ≤ sqE ξ ≤ (b + p) |ξ|² for the sup norm, and along J ξ = (x, -y) the derivatives are
2 sqX and -2 sqY. The model function is h(z) - sqX ξ + sqY ξ with h(z) = Ψ(z, 0), the cutoff is
χ(z, ξ) = χ₀(z) Φ(sqE ξ) with the logarithmic cutoff Φ, and the deformed function is

  G = Ψ + χ (model - Ψ).

At a point over K₀ with |ξ| ≤ R, if the split descent estimate holds with constants c, κ, the
fibre growth |Ψ(z, ξ) - Ψ(z, 0)| ≤ C₁ |ξ|² holds, |Dχ₀| ≤ B, |V₀| ≤ κ on K₀, and
(C₁ + 1)(B κ + 2 M / λ) ≤ c* / 2 with c* = min(c / (b + p + 1), 2), then

  DG(z, ξ)(V₀(z), J ξ) ≤ DΨ(z, 0)(V₀(z), 0) - (c* / 2) sqE ξ,

so G decreases along the split field, strictly where ξ ≠ 0 or the root field decreases the root
functional. Where χ = 1, G is exactly the product model. -/

@[expose] public section

namespace Finsler.LabelDeform

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LogCutoff
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
set_option maxSynthPendingDepth 3

section Squares

variable {b p : ℕ}

/-- The negative coefficients in Euclidean space. -/
def eucX : (Fin b → ℝ) × (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin b) :=
  ((EuclideanSpace.equiv (Fin b) ℝ).symm : (Fin b → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin b)).comp
    (ContinuousLinearMap.fst ℝ (Fin b → ℝ) (Fin p → ℝ))

/-- The positive coefficients in Euclidean space. -/
def eucY : (Fin b → ℝ) × (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ((EuclideanSpace.equiv (Fin p) ℝ).symm : (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p)).comp
    (ContinuousLinearMap.snd ℝ (Fin b → ℝ) (Fin p → ℝ))

theorem eucX_apply (ξ : (Fin b → ℝ) × (Fin p → ℝ)) (i : Fin b) : eucX ξ i = ξ.1 i := rfl

theorem eucY_apply (ξ : (Fin b → ℝ) × (Fin p → ℝ)) (j : Fin p) : eucY ξ j = ξ.2 j := rfl

/-- The Euclidean square of the negative coefficients. -/
def sqX (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : ℝ := ‖eucX ξ‖ ^ 2

/-- The Euclidean square of the positive coefficients. -/
def sqY (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : ℝ := ‖eucY ξ‖ ^ 2

/-- The Euclidean square of the coefficients. -/
def sqE (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : ℝ := sqX ξ + sqY ξ

theorem sqX_nonneg (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : 0 ≤ sqX ξ := sq_nonneg _

theorem sqY_nonneg (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : 0 ≤ sqY ξ := sq_nonneg _

theorem sqE_nonneg (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : 0 ≤ sqE ξ :=
  add_nonneg (sqX_nonneg ξ) (sqY_nonneg ξ)

theorem sqX_contDiff : ContDiff ℝ ∞ (sqX (b := b) (p := p)) :=
  (contDiff_norm_sq ℝ).comp eucX.contDiff

theorem sqY_contDiff : ContDiff ℝ ∞ (sqY (b := b) (p := p)) :=
  (contDiff_norm_sq ℝ).comp eucY.contDiff

theorem sqE_contDiff : ContDiff ℝ ∞ (sqE (b := b) (p := p)) :=
  sqX_contDiff.add sqY_contDiff

theorem eucX_swapJ (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : eucX (swapJ ξ) = eucX ξ := by
  rw [swapJ_apply]
  rfl

theorem eucY_swapJ (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : eucY (swapJ ξ) = -eucY ξ := by
  rw [swapJ_apply]
  rw [show ((ξ.1, -ξ.2) : (Fin b → ℝ) × (Fin p → ℝ)) = (ξ.1, 0) - (0, ξ.2) by
    ext <;> simp, map_sub]
  have h1 : eucY ((ξ.1, 0) : (Fin b → ℝ) × (Fin p → ℝ)) = 0 := by
    change ((EuclideanSpace.equiv (Fin p) ℝ).symm : (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p))
      0 = 0
    exact map_zero _
  have h2 : eucY ((0, ξ.2) : (Fin b → ℝ) × (Fin p → ℝ)) = eucY ξ := rfl
  rw [h1, h2, zero_sub]

/-- The derivative of sqX along J ξ is 2 sqX. -/
theorem fderiv_sqX_swapJ (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    fderiv ℝ sqX ξ (swapJ ξ) = 2 * sqX ξ := by
  have h : HasFDerivAt (fun ξ => ‖eucX ξ‖ ^ 2) (2 • (innerSL ℝ (eucX ξ)).comp eucX) ξ :=
    eucX.hasFDerivAt.norm_sq
  rw [show (sqX : (Fin b → ℝ) × (Fin p → ℝ) → ℝ) = fun ξ => ‖eucX ξ‖ ^ 2 from rfl, h.fderiv]
  change 2 • ⟪eucX ξ, eucX (swapJ ξ)⟫ = 2 * sqX ξ
  rw [eucX_swapJ, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
  rfl

/-- The derivative of sqY along J ξ is -2 sqY. -/
theorem fderiv_sqY_swapJ (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    fderiv ℝ sqY ξ (swapJ ξ) = -(2 * sqY ξ) := by
  have h : HasFDerivAt (fun ξ => ‖eucY ξ‖ ^ 2) (2 • (innerSL ℝ (eucY ξ)).comp eucY) ξ :=
    eucY.hasFDerivAt.norm_sq
  rw [show (sqY : (Fin b → ℝ) × (Fin p → ℝ) → ℝ) = fun ξ => ‖eucY ξ‖ ^ 2 from rfl, h.fderiv]
  change 2 • ⟪eucY ξ, eucY (swapJ ξ)⟫ = -(2 * sqY ξ)
  rw [eucY_swapJ, inner_neg_right, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
  unfold sqY
  ring

/-- The derivative of sqE along J ξ is bounded by 2 sqE. -/
theorem abs_fderiv_sqE_swapJ (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    |fderiv ℝ sqE ξ (swapJ ξ)| ≤ 2 * sqE ξ := by
  have h : fderiv ℝ sqE ξ = fderiv ℝ sqX ξ + fderiv ℝ sqY ξ :=
    fderiv_add (sqX_contDiff.differentiable (by simp) ξ) (sqY_contDiff.differentiable (by simp) ξ)
  rw [h, add_apply, fderiv_sqX_swapJ, fderiv_sqY_swapJ]
  have h1 := sqX_nonneg ξ
  have h2 := sqY_nonneg ξ
  unfold sqE
  rw [abs_le]
  constructor <;> linarith

theorem sq_norm_le_sqE (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : ‖ξ‖ ^ 2 ≤ sqE ξ := by
  have h1 : ‖ξ.1‖ ≤ ‖eucX ξ‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [← eucX_apply]
    exact PiLp.norm_apply_le (eucX ξ) i
  have h2 : ‖ξ.2‖ ≤ ‖eucY ξ‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
    rw [← eucY_apply]
    exact PiLp.norm_apply_le (eucY ξ) j
  rw [Prod.norm_def]
  have h3 : ‖ξ.1‖ ^ 2 ≤ sqX ξ := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : ‖ξ.2‖ ^ 2 ≤ sqY ξ := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h5 := sqX_nonneg ξ
  have h6 := sqY_nonneg ξ
  unfold sqE
  rcases le_total ‖ξ.1‖ ‖ξ.2‖ with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

theorem sqX_le (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : sqX ξ ≤ b * ‖ξ‖ ^ 2 := by
  unfold sqX
  rw [EuclideanSpace.real_norm_sq_eq]
  have h : ∀ i, (eucX ξ i) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    intro i
    rw [eucX_apply, ← sq_abs]
    have h1 : |ξ.1 i| ≤ ‖ξ.1‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm ξ.1 i
    have h2 : ‖ξ.1‖ ≤ ‖ξ‖ := norm_fst_le ξ
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  calc ∑ i, (eucX ξ i) ^ 2 ≤ ∑ _i : Fin b, ‖ξ‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = b * ‖ξ‖ ^ 2 := by simp

theorem sqY_le (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : sqY ξ ≤ p * ‖ξ‖ ^ 2 := by
  unfold sqY
  rw [EuclideanSpace.real_norm_sq_eq]
  have h : ∀ j, (eucY ξ j) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    intro j
    rw [eucY_apply, ← sq_abs]
    have h1 : |ξ.2 j| ≤ ‖ξ.2‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm ξ.2 j
    have h2 : ‖ξ.2‖ ≤ ‖ξ‖ := norm_snd_le ξ
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  calc ∑ j, (eucY ξ j) ^ 2 ≤ ∑ _j : Fin p, ‖ξ‖ ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = p * ‖ξ‖ ^ 2 := by simp

theorem sqE_le (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : sqE ξ ≤ (b + p) * ‖ξ‖ ^ 2 := by
  have h1 := sqX_le ξ
  have h2 := sqY_le ξ
  unfold sqE
  linarith

end Squares

section Cutoff

variable {n N b p : ℕ}

/-- The cutoff χ₀(z) Φ(sqE ξ) in frame coordinates. -/
def cutoff (χ₀ : (ZMod N → Ambient n) → ℝ) (r lam : ℝ)
    (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) : ℝ :=
  χ₀ q.1 * logCut r lam (sqE q.2)

variable {χ₀ : (ZMod N → Ambient n) → ℝ} {r lam : ℝ}

theorem cutoff_nonneg (hχ0 : ∀ z, 0 ≤ χ₀ z)
    (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) : 0 ≤ cutoff χ₀ r lam q :=
  mul_nonneg (hχ0 _) (logCut_nonneg _ _ _)

theorem cutoff_le_one (hχ1 : ∀ z, χ₀ z ≤ 1)
    (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) : cutoff χ₀ r lam q ≤ 1 := by
  have h := mul_le_mul (hχ1 q.1) (logCut_le_one r lam (sqE q.2)) (logCut_nonneg _ _ _) zero_le_one
  rwa [one_mul] at h

theorem cutoff_eq_one (hr : r ≠ 0) (hlam : 0 < lam)
    {q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))} (hz : χ₀ q.1 = 1)
    (hξ : sqE q.2 ≤ r ^ 2) : cutoff χ₀ r lam q = 1 := by
  unfold cutoff
  rw [hz, logCut_of_le hr hlam (sqE_nonneg _) hξ, one_mul]

theorem cutoff_eq_zero_of_ge (hr : r ≠ 0) (hlam : 0 < lam)
    {q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))}
    (hξ : r ^ 2 * Real.exp lam ≤ sqE q.2) : cutoff χ₀ r lam q = 0 := by
  unfold cutoff
  rw [logCut_of_ge hr hlam hξ, mul_zero]

theorem cutoff_eq_zero_of_base {q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))}
    (hz : χ₀ q.1 = 0) : cutoff χ₀ r lam q = 0 := by
  unfold cutoff
  rw [hz, zero_mul]

theorem cutoff_contDiff [NeZero N] (hr : r ≠ 0) (hlam : 0 < lam) (hχ : ContDiff ℝ ∞ χ₀) :
    ContDiff ℝ ∞ (cutoff (b := b) (p := p) χ₀ r lam) :=
  (hχ.comp contDiff_fst).mul
    ((logCut_comp_contDiff hr hlam sqE_contDiff sqE_nonneg).comp contDiff_snd)

/-- The derivative of the cutoff along (v, J ξ) is at most |Dχ₀(z)| |v| + 2 M / λ. -/
theorem abs_fderiv_cutoff_le [NeZero N] (hr : r ≠ 0) (hlam : 0 < lam) (hχ : ContDiff ℝ ∞ χ₀)
    (hχ0 : ∀ z, 0 ≤ χ₀ z) (hχ1 : ∀ z, χ₀ z ≤ 1) {M : ℝ}
    (hM : ∀ x, |deriv Real.smoothTransition x| ≤ M) (z : ZMod N → Ambient n)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) (v : ZMod N → Ambient n) :
    |fderiv ℝ (cutoff χ₀ r lam) (z, ξ) (v, swapJ ξ)| ≤ ‖fderiv ℝ χ₀ z‖ * ‖v‖ + 2 * M / lam := by
  have hΦ : ContDiff ℝ ∞ fun ξ : (Fin b → ℝ) × (Fin p → ℝ) => logCut r lam (sqE ξ) :=
    logCut_comp_contDiff hr hlam sqE_contDiff sqE_nonneg
  have h1 : HasFDerivAt (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) => χ₀ q.1)
      ((fderiv ℝ χ₀ z).comp (ContinuousLinearMap.fst ℝ _ _)) (z, ξ) :=
    ((hχ.differentiable (by simp) z).hasFDerivAt).comp (z, ξ) (hasFDerivAt_fst (𝕜 := ℝ) (p := (z, ξ)))
  have h2 : HasFDerivAt ((fun ξ : (Fin b → ℝ) × (Fin p → ℝ) => logCut r lam (sqE ξ)) ∘
      (Prod.snd : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) → (Fin b → ℝ) × (Fin p → ℝ)))
      ((fderiv ℝ (fun ξ => logCut r lam (sqE ξ)) ξ).comp (ContinuousLinearMap.snd ℝ _ _)) (z, ξ) :=
    HasFDerivAt.comp (z, ξ) (g := fun ξ : (Fin b → ℝ) × (Fin p → ℝ) => logCut r lam (sqE ξ))
      ((hΦ.differentiable (by simp) ξ).hasFDerivAt) (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, ξ)))
  have h3 : HasFDerivAt (cutoff χ₀ r lam)
      (χ₀ z • (fderiv ℝ (fun ξ => logCut r lam (sqE ξ)) ξ).comp (ContinuousLinearMap.snd ℝ _ _) +
        logCut r lam (sqE ξ) • (fderiv ℝ χ₀ z).comp (ContinuousLinearMap.fst ℝ _ _)) (z, ξ) :=
    h1.mul h2
  rw [h3.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hb1 : |fderiv ℝ (fun ξ => logCut r lam (sqE ξ)) ξ (swapJ ξ)| ≤ 2 * M / lam :=
    abs_fderiv_logCut_comp_le hr hlam zero_le_two hM sqE_contDiff sqE_nonneg ξ (swapJ ξ)
      (abs_fderiv_sqE_swapJ ξ)
  have hb2 : |fderiv ℝ χ₀ z v| ≤ ‖fderiv ℝ χ₀ z‖ * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact ContinuousLinearMap.le_opNorm _ _
  have hc0 := hχ0 z
  have hc1 := hχ1 z
  have hl0 := logCut_nonneg r lam (sqE ξ)
  have hl1 := logCut_le_one r lam (sqE ξ)
  calc |χ₀ z * fderiv ℝ (fun ξ => logCut r lam (sqE ξ)) ξ (swapJ ξ) +
        logCut r lam (sqE ξ) * fderiv ℝ χ₀ z v|
      ≤ |χ₀ z * fderiv ℝ (fun ξ => logCut r lam (sqE ξ)) ξ (swapJ ξ)| +
        |logCut r lam (sqE ξ) * fderiv ℝ χ₀ z v| := abs_add_le _ _
    _ ≤ 1 * (2 * M / lam) + 1 * (‖fderiv ℝ χ₀ z‖ * ‖v‖) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg hl0]
        exact add_le_add (mul_le_mul hc1 hb1 (abs_nonneg _) zero_le_one)
          (mul_le_mul hl1 hb2 (abs_nonneg _) zero_le_one)
    _ = ‖fderiv ℝ χ₀ z‖ * ‖v‖ + 2 * M / lam := by ring

end Cutoff

section Deform

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)

/-- The product model in frame coordinates: Ψ(z, 0) - |x|² + |y|². -/
def model (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) : ℝ :=
  psi m N F G₁ G₂ (q.1, 0) - sqX q.2 + sqY q.2

/-- The deformed function Ψ + χ (model - Ψ). -/
def deformG (χ₀ : (ZMod N → Ambient n) → ℝ) (r lam : ℝ)
    (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) : ℝ :=
  psi m N F G₁ G₂ q + cutoff χ₀ r lam q * (model m N F G₁ G₂ q - psi m N F G₁ G₂ q)

/-- Where the cutoff is 1 the deformed function is the model. -/
theorem deformG_of_cutoff_eq_one {χ₀ : (ZMod N → Ambient n) → ℝ} {r lam : ℝ}
    {q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))} (hq : cutoff χ₀ r lam q = 1) :
    deformG m N F G₁ G₂ χ₀ r lam q = model m N F G₁ G₂ q := by
  unfold deformG
  rw [hq, one_mul, add_sub_cancel]

/-- Where the cutoff is 0 the deformed function is Ψ. -/
theorem deformG_of_cutoff_eq_zero {χ₀ : (ZMod N → Ambient n) → ℝ} {r lam : ℝ}
    {q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))} (hq : cutoff χ₀ r lam q = 0) :
    deformG m N F G₁ G₂ χ₀ r lam q = psi m N F G₁ G₂ q := by
  unfold deformG
  rw [hq, zero_mul, add_zero]

/-- The derivative of the model along (v, J ξ): DΨ(z, 0)(v, 0) - 2 sqE ξ. -/
theorem fderiv_model_swapJ {z : ZMod N → Ambient n}
    (hd : DifferentiableAt ℝ (psi m N F G₁ G₂) (z, 0)) (ξ : (Fin b → ℝ) × (Fin p → ℝ))
    (v : ZMod N → Ambient n) :
    fderiv ℝ (model m N F G₁ G₂) (z, ξ) (v, swapJ ξ) =
      fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - 2 * sqE ξ := by
  set L : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) →L[ℝ]
      (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) :=
    (ContinuousLinearMap.inl ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ))).comp
      (ContinuousLinearMap.fst ℝ _ _) with hL
  have h0 : HasFDerivAt (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
      psi m N F G₁ G₂ (q.1, 0)) ((fderiv ℝ (psi m N F G₁ G₂) (z, 0)).comp L) (z, ξ) :=
    HasFDerivAt.comp (z, ξ) (g := psi m N F G₁ G₂) (f := L) hd.hasFDerivAt L.hasFDerivAt
  have hX : HasFDerivAt (sqX ∘ (Prod.snd : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) →
      (Fin b → ℝ) × (Fin p → ℝ))) ((fderiv ℝ sqX ξ).comp (ContinuousLinearMap.snd ℝ _ _)) (z, ξ) :=
    HasFDerivAt.comp (z, ξ) (g := sqX) ((sqX_contDiff.differentiable (by simp) ξ).hasFDerivAt)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, ξ)))
  have hY : HasFDerivAt (sqY ∘ (Prod.snd : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) →
      (Fin b → ℝ) × (Fin p → ℝ))) ((fderiv ℝ sqY ξ).comp (ContinuousLinearMap.snd ℝ _ _)) (z, ξ) :=
    HasFDerivAt.comp (z, ξ) (g := sqY) ((sqY_contDiff.differentiable (by simp) ξ).hasFDerivAt)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, ξ)))
  have h : HasFDerivAt (model m N F G₁ G₂)
      ((fderiv ℝ (psi m N F G₁ G₂) (z, 0)).comp L -
        (fderiv ℝ sqX ξ).comp (ContinuousLinearMap.snd ℝ _ _) +
          (fderiv ℝ sqY ξ).comp (ContinuousLinearMap.snd ℝ _ _)) (z, ξ) :=
    (h0.sub hX).add hY
  rw [h.fderiv]
  simp only [add_apply, sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_snd', hL, ContinuousLinearMap.coe_fst', ContinuousLinearMap.inl_apply]
  rw [fderiv_sqX_swapJ, fderiv_sqY_swapJ]
  unfold sqE
  ring

/-- The model differs from Ψ by at most (C₁ + 1) sqE on the region of the fibre growth bound. -/
theorem abs_model_sub_psi_le {K₀ : Set (ZMod N → Ambient n)} {R C₁ : ℝ}
    (hquad : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| ≤ C₁ * ‖ξ‖ ^ 2)
    (hC₁ : 0 ≤ C₁) {z : ZMod N → Ambient n} (hz : z ∈ K₀) {ξ : (Fin b → ℝ) × (Fin p → ℝ)}
    (hξ : ‖ξ‖ ≤ R) :
    |model m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, ξ)| ≤ (C₁ + 1) * sqE ξ := by
    have h1 := hquad z hz ξ hξ
    have h2 := sq_norm_le_sqE ξ
    have h3 := sqX_nonneg ξ
    have h4 := sqY_nonneg ξ
    have e2 : model m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, ξ) =
        -(psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)) + (sqY ξ - sqX ξ) := by
      unfold model
      ring
    rw [e2]
    have h5 : |sqY ξ - sqX ξ| ≤ sqE ξ := by
      unfold sqE
      rw [abs_le]
      constructor <;> linarith
    calc |-(psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)) + (sqY ξ - sqX ξ)|
        ≤ |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| + |sqY ξ - sqX ξ| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg]
      _ ≤ C₁ * ‖ξ‖ ^ 2 + sqE ξ := add_le_add h1 h5
      _ ≤ C₁ * sqE ξ + sqE ξ := by
          have := mul_le_mul_of_nonneg_left h2 hC₁
          linarith
      _ = (C₁ + 1) * sqE ξ := by ring

/-- **Descent of the deformed function.** -/
theorem deformG_descent (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K₀ : Set (ZMod N → Ambient n)} {R κ c C₁ : ℝ}
    (hest : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2)
    (hquad : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| ≤ C₁ * ‖ξ‖ ^ 2)
    (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    {χ₀ : (ZMod N → Ambient n) → ℝ} (hχ : ContDiff ℝ ∞ χ₀) (hχ0 : ∀ z, 0 ≤ χ₀ z)
    (hχ1 : ∀ z, χ₀ z ≤ 1) {B : ℝ} (hB : ∀ z, ‖fderiv ℝ χ₀ z‖ ≤ B)
    {r lam M : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) (hM : ∀ x, |deriv Real.smoothTransition x| ≤ M)
    (hsmall : (C₁ + 1) * (B * κ + 2 * M / lam) ≤ min (c / (b + p + 1)) 2 / 2)
    {z : ZMod N → Ambient n} (hz : z ∈ K₀) {ξ : (Fin b → ℝ) × (Fin p → ℝ)} (hξ : ‖ξ‖ ≤ R)
    {v : ZMod N → Ambient n} (hv : ‖v‖ ≤ κ) :
    fderiv ℝ (deformG m N F G₁ G₂ χ₀ r lam) (z, ξ) (v, swapJ ξ) ≤
      fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - min (c / (b + p + 1)) 2 / 2 * sqE ξ := by
  have hR : 0 ≤ R := (norm_nonneg ξ).trans hξ
  have hcoord := coord_contDiff m N G₁ G₂ hG₁ hG₂
  have hpsiAt : ∀ ζ : (Fin b → ℝ) × (Fin p → ℝ), ‖ζ‖ ≤ R →
      ContDiffAt ℝ 3 (psi m N F G₁ G₂) (z, ζ) := fun ζ hζ =>
    ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) (z, ζ) (hest z hz ζ hζ).1
      (hcoord.contDiffAt.of_le (by simp))
  have hd : DifferentiableAt ℝ (psi m N F G₁ G₂) (z, ξ) :=
    (hpsiAt ξ hξ).differentiableAt (by norm_num)
  have hd0 : DifferentiableAt ℝ (psi m N F G₁ G₂) (z, 0) :=
    (hpsiAt 0 (by rw [norm_zero]; exact hR)).differentiableAt (by norm_num)
  have hdM : DifferentiableAt ℝ (model m N F G₁ G₂) (z, ξ) := by
    have h1 : DifferentiableAt ℝ (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
        psi m N F G₁ G₂ (q.1, 0)) (z, ξ) := by
      have hL : DifferentiableAt ℝ (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
          ((q.1, 0) : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)))) (z, ξ) :=
        differentiableAt_fst.prodMk (differentiableAt_const _)
      exact DifferentiableAt.comp (z, ξ) (g := psi m N F G₁ G₂) hd0 hL
    have h2 : DifferentiableAt ℝ (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
        sqX q.2) (z, ξ) := (sqX_contDiff.differentiable (by simp) _).comp (z, ξ) differentiableAt_snd
    have h3 : DifferentiableAt ℝ (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
        sqY q.2) (z, ξ) := (sqY_contDiff.differentiable (by simp) _).comp (z, ξ) differentiableAt_snd
    exact (h1.sub h2).add h3
  have hdχ : DifferentiableAt ℝ (cutoff (b := b) (p := p) χ₀ r lam) (z, ξ) :=
    (cutoff_contDiff hr hlam hχ).differentiable (by simp) _
  have hform := fderiv_deform hd hdM hdχ (v, swapJ ξ)
  have e : (fun y => psi m N F G₁ G₂ y + cutoff χ₀ r lam y *
      (model m N F G₁ G₂ y - psi m N F G₁ G₂ y)) = deformG m N F G₁ G₂ χ₀ r lam := rfl
  rw [e] at hform
  rw [hform]
  set A := fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) with hA
  set cs := min (c / (b + p + 1)) 2 with hcs
  have hq0 := sqE_nonneg ξ
  have hcs2 : cs ≤ 2 := min_le_right _ _
  have hcs1 : cs ≤ c / (b + p + 1) := min_le_left _ _
  have hcq : c / (b + p + 1) * sqE ξ ≤ c * ‖ξ‖ ^ 2 := by
    have hpos : 0 < (b : ℝ) + p + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have h1 := sqE_le ξ
    have h2 : sqE ξ ≤ ((b : ℝ) + p + 1) * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
    have := mul_le_mul_of_nonneg_left h2 hc.le
    linarith [mul_comm (c * ‖ξ‖ ^ 2) ((b : ℝ) + p + 1), mul_assoc c ((b : ℝ) + p + 1) (‖ξ‖ ^ 2),
      mul_comm c ((b : ℝ) + p + 1)]
  have hΨ : fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤ A - cs * sqE ξ := by
    have h1 := (hest z hz ξ hξ).2 v hv
    have h2 : cs * sqE ξ ≤ c / (b + p + 1) * sqE ξ := mul_le_mul_of_nonneg_right hcs1 hq0
    linarith
  have hMd : fderiv ℝ (model m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤ A - cs * sqE ξ := by
    rw [fderiv_model_swapJ m N F G₁ G₂ hd0 ξ v]
    have h2 : cs * sqE ξ ≤ 2 * sqE ξ := mul_le_mul_of_nonneg_right hcs2 hq0
    linarith
  have hδ := abs_model_sub_psi_le m N F G₁ G₂ hquad hC₁ hz hξ
  have hdc : |fderiv ℝ (cutoff χ₀ r lam) (z, ξ) (v, swapJ ξ)| ≤ B * κ + 2 * M / lam := by
    have h1 := abs_fderiv_cutoff_le hr hlam hχ hχ0 hχ1 hM z ξ v
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z)
    have h2 : ‖fderiv ℝ χ₀ z‖ * ‖v‖ ≤ B * κ :=
      mul_le_mul (hB z) hv (norm_nonneg _) hB0
    linarith
  exact deform_le (cutoff_nonneg hχ0 _) (cutoff_le_one hχ1 _) hΨ hMd hδ hdc hsmall hq0

end Deform

end

end Finsler.LabelDeform
