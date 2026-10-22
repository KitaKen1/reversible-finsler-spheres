module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual local coordinate covariance of Euler--Lagrange residuals.
The Lagrangian is pulled back by the genuine position--velocity map of phi.
Only local C² hypotheses are used, so the result can later be applied to a
chart inverse on its open domain. This generic calculus result alone does not
complete the standard-sphere geodesic comparison. -/

@[expose] public section

namespace Finsler.EulerCovariance

open Function Filter
open scoped ContDiff Topology

noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def positionTerm (L : A × A → ℝ) (z : A × A) : A →L[ℝ] ℝ :=
  (fderiv ℝ L z).comp (ContinuousLinearMap.inl ℝ A A)

def velocityTerm (L : A × A → ℝ) (z : A × A) : A →L[ℝ] ℝ :=
  (fderiv ℝ L z).comp (ContinuousLinearMap.inr ℝ A A)

theorem differential_split (L : A × A → ℝ) (z : A × A) (a b : A) :
    fderiv ℝ L z (a, b) = positionTerm L z a + velocityTerm L z b := by
  change _ = fderiv ℝ L z (a, 0) + fderiv ℝ L z (0, b)
  rw [← map_add]
  simp

def jetMap (φ : E → A) (z : E × E) : A × A :=
  (φ z.1, fderiv ℝ φ z.1 z.2)

def pullback (L : A × A → ℝ) (φ : E → A) : E × E → ℝ := L ∘ jetMap φ

def jetDifferential (φ : E → A) (z : E × E) : E × E →L[ℝ] A × A :=
  ((fderiv ℝ φ z.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
    ((fderiv ℝ φ z.1).comp (ContinuousLinearMap.snd ℝ E E) +
      ((fderiv ℝ (fderiv ℝ φ) z.1).comp (ContinuousLinearMap.fst ℝ E E)).flip z.2)

theorem jet_hasFDerivAt {φ : E → A} {z : E × E} (hφ : ContDiffAt ℝ 2 φ z.1) :
    HasFDerivAt (jetMap φ) (jetDifferential φ z) z := by
  have hp := (hφ.differentiableAt (by norm_num)).hasFDerivAt.comp z hasFDerivAt_fst
  have hv := (((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp z hasFDerivAt_fst).clm_apply hasFDerivAt_snd
  exact hp.prodMk hv

theorem jet_smoothAt {φ : E → A} {z : E × E} (hφ : ContDiffAt ℝ 2 φ z.1) :
    ContDiffAt ℝ 1 (jetMap φ) z :=
  ((hφ.of_le (by norm_num)).comp z contDiffAt_fst).prodMk
    (((hφ.fderiv_right (m := 1) (by norm_num)).comp z contDiffAt_fst).clm_apply
      contDiffAt_snd)

theorem pullback_smoothAt {L : A × A → ℝ} {φ : E → A} {z : E × E}
    (hφ : ContDiffAt ℝ 2 φ z.1) (hL : ContDiffAt ℝ 1 L (jetMap φ z)) :
    ContDiffAt ℝ 1 (pullback L φ) z := hL.comp z (jet_smoothAt hφ)

theorem pullback_fderiv {L : A × A → ℝ} {φ : E → A} {z : E × E}
    (hφ : ContDiffAt ℝ 2 φ z.1) (hL : ContDiffAt ℝ 1 L (jetMap φ z)) :
    fderiv ℝ (pullback L φ) z = (fderiv ℝ L (jetMap φ z)).comp (jetDifferential φ z) :=
  ((hL.differentiableAt (by norm_num)).hasFDerivAt.comp z (jet_hasFDerivAt hφ)).fderiv

theorem pullback_position {L : A × A → ℝ} {φ : E → A} {z : E × E}
    (hφ : ContDiffAt ℝ 2 φ z.1) (hL : ContDiffAt ℝ 1 L (jetMap φ z)) (a : E) :
    positionTerm (pullback L φ) z a =
      positionTerm L (jetMap φ z) (fderiv ℝ φ z.1 a) +
        velocityTerm L (jetMap φ z) (fderiv ℝ (fderiv ℝ φ) z.1 a z.2) := by
  have he := congrArg (fun D : E × E →L[ℝ] ℝ => D (a, 0)) (pullback_fderiv hφ hL)
  simp [jetDifferential] at he
  change fderiv ℝ (pullback L φ) z (a, 0) = _
  rw [he]
  exact differential_split _ _ _ _

theorem pullback_velocity {L : A × A → ℝ} {φ : E → A} {z : E × E}
    (hφ : ContDiffAt ℝ 2 φ z.1) (hL : ContDiffAt ℝ 1 L (jetMap φ z)) :
    velocityTerm (pullback L φ) z = (velocityTerm L (jetMap φ z)).comp (fderiv ℝ φ z.1) := by
  ext a
  have he := congrArg (fun D : E × E →L[ℝ] ℝ => D (0, a)) (pullback_fderiv hφ hL)
  simpa [velocityTerm, jetDifferential] using he

def curveJet (x : ℝ → E) (t : ℝ) : E × E := (x t, deriv x t)

theorem curveJet_smoothAt {x : ℝ → E} {t : ℝ} (hx : ContDiffAt ℝ 2 x t) :
    ContDiffAt ℝ 1 (curveJet x) t :=
  (hx.of_le (by norm_num)).prodMk (hx.derivWithin (m := 1) (by norm_num))

theorem jetMap_curveJet {φ : E → A} {x : ℝ → E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (x t)) (hx : DifferentiableAt ℝ x t) :
    jetMap φ (curveJet x t) = curveJet (φ ∘ x) t := by
  apply Prod.ext
  · rfl
  · exact (hφ.hasFDerivAt.comp_hasDerivAt t hx.hasDerivAt).deriv.symm

def momentum (L : E × E → ℝ) (x : ℝ → E) (t : ℝ) : E →L[ℝ] ℝ :=
  velocityTerm L (curveJet x t)

def residual (L : E × E → ℝ) (x : ℝ → E) (t : ℝ) : E →L[ℝ] ℝ :=
  positionTerm L (curveJet x t) - deriv (momentum L x) t

theorem momentum_smoothAt {L : E × E → ℝ} {x : ℝ → E} {t : ℝ}
    (hx : ContDiffAt ℝ 2 x t) (hL : ContDiffAt ℝ 2 L (curveJet x t)) :
    ContDiffAt ℝ 1 (momentum L x) t :=
  (((hL.fderiv_right (m := 1) (by norm_num)).comp t (curveJet_smoothAt hx)).clm_comp
    contDiffAt_const)

theorem curveJet_congr_eventually {x y : ℝ → E} {t : ℝ} (h : x =ᶠ[𝓝 t] y) :
    curveJet x =ᶠ[𝓝 t] curveJet y := by
  filter_upwards [h, h.deriv] with u hu hdu
  simp only [curveJet, hu, hdu]

theorem residual_congr_eventually (L : E × E → ℝ) {x y : ℝ → E} {t : ℝ}
    (h : x =ᶠ[𝓝 t] y) : residual L x t = residual L y t := by
  have hj := curveJet_congr_eventually h
  have hm : momentum L x =ᶠ[𝓝 t] momentum L y := hj.fun_comp (velocityTerm L)
  rw [residual, residual, hj.eq_of_nhds, hm.deriv_eq]

/-- The actual coordinate momentum has the actual differentiated pullback.
The pointwise identity is transported on a neighborhood, not just at t. -/
theorem momentum_pullback_hasDerivAt {L : A × A → ℝ} {φ : E → A} {x : ℝ → E} {t : ℝ}
    (hφ : ContDiffAt ℝ 2 φ (x t)) (hx : ContDiffAt ℝ 2 x t)
    (hL : ContDiffAt ℝ 2 L (jetMap φ (curveJet x t))) :
    HasDerivAt (momentum (pullback L φ) x)
      ((deriv (momentum L (φ ∘ x)) t).comp (fderiv ℝ φ (x t)) +
        (momentum L (φ ∘ x) t).comp (fderiv ℝ (fderiv ℝ φ) (x t) (deriv x t))) t := by
  have hj := jetMap_curveJet (hφ.differentiableAt (by norm_num))
    (hx.differentiableAt (by norm_num))
  have ha : ContDiffAt ℝ 2 (φ ∘ x) t := hφ.comp t hx
  have hLa : ContDiffAt ℝ 2 L (curveJet (φ ∘ x) t) := by
    rw [← hj]
    exact hL
  have hQ := ((momentum_smoothAt ha hLa).differentiableAt (by norm_num)).hasDerivAt
  have hB := ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      ((hx.differentiableAt (by norm_num)).hasDerivAt)
  have hProduct := hQ.clm_comp hB
  have he : momentum (pullback L φ) x =ᶠ[𝓝 t]
      (fun u => (momentum L (φ ∘ x) u).comp (fderiv ℝ φ (x u))) := by
    have hEφ := hx.continuousAt.tendsto.eventually (hφ.eventually (by simp))
    have hEx := hx.eventually (by simp)
    have hEL := (curveJet_smoothAt ha).continuousAt.tendsto.eventually
      (hLa.eventually (by simp))
    filter_upwards [hEφ, hEx, hEL] with u huφ hux huL
    have hju := jetMap_curveJet (huφ.differentiableAt (by norm_num))
      (hux.differentiableAt (by norm_num))
    have huLJ : ContDiffAt ℝ 1 L (jetMap φ (curveJet x u)) := by
      rw [hju]
      exact huL.of_le (by norm_num)
    change velocityTerm (pullback L φ) (curveJet x u) =
      (velocityTerm L (curveJet (φ ∘ x) u)).comp (fderiv ℝ φ (x u))
    rw [pullback_velocity huφ huLJ, hju]
    rfl
  exact hProduct.congr_of_eventuallyEq he

/-- The second derivatives of the coordinate map cancel by their actual
symmetry. This is covariance of the actual Euler residual, not an assumption. -/
theorem residual_pullback {L : A × A → ℝ} {φ : E → A} {x : ℝ → E} {t : ℝ}
    (hφ : ContDiffAt ℝ 2 φ (x t)) (hx : ContDiffAt ℝ 2 x t)
    (hL : ContDiffAt ℝ 2 L (jetMap φ (curveJet x t))) :
    residual (pullback L φ) x t = (residual L (φ ∘ x) t).comp (fderiv ℝ φ (x t)) := by
  have hj := jetMap_curveJet (hφ.differentiableAt (by norm_num))
    (hx.differentiableAt (by norm_num))
  have hQ := (momentum_pullback_hasDerivAt hφ hx hL).deriv
  ext a
  have hP := pullback_position hφ (hL.of_le (by norm_num)) a
  change positionTerm (pullback L φ) (curveJet x t) a -
    deriv (momentum (pullback L φ) x) t a =
      positionTerm L (curveJet (φ ∘ x) t) (fderiv ℝ φ (x t) a) -
        deriv (momentum L (φ ∘ x)) t (fderiv ℝ φ (x t) a)
  rw [hP, hQ]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [hj]
  simp only [curveJet]
  rw [(hφ.isSymmSndFDerivAt (by simp)).eq a (deriv x t)]
  simp only [momentum, curveJet]
  ring

end

end Finsler.EulerCovariance
