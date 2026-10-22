module

public import Finsler.Analysis.EulerCovariance
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The spray of a Lagrangian on a finite-dimensional space. Where the velocity Hessian H is
injective (positive definite), it is a continuous linear equivalence onto the dual, and the
spray is the acceleration H⁻¹(∂ₓL − (∂ₓ∂ᵥL)v). A C² curve whose acceleration equals the spray
of its jet has vanishing Euler–Lagrange residual. The spray is C^k where L is C^(k+2), and it
is quadratic in the velocity when L is. -/

@[expose] public section

namespace Finsler.LagrangianSpray

open Finsler.EulerCovariance Function Filter
open scoped ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The velocity Hessian ∂ᵥ∂ᵥL at a jet. -/
def velocityHessian (L : E × E → ℝ) (z : E × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun w => velocityTerm L (z.1, w)) z.2

/-- The mixed term (∂ₓ∂ᵥL)(v) at a jet (x,v). -/
def mixedTerm (L : E × E → ℝ) (z : E × E) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => velocityTerm L (y, z.2)) z.1 z.2

/-- The spray: the acceleration a with H a = ∂ₓL − (∂ₓ∂ᵥL)v. -/
def spray (L : E × E → ℝ) (z : E × E) : E :=
  ContinuousLinearMap.inverse (velocityHessian L z) (positionTerm L z - mixedTerm L z)

theorem finrank_dual_eq : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- An injective map to the dual is a continuous linear equivalence. -/
def hessianEquiv (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : Injective H) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearMap.linearEquivOfInjective (H : E →ₗ[ℝ] E →L[ℝ] ℝ) hH
    finrank_dual_eq.symm).toContinuousLinearEquiv

theorem hessianEquiv_coe (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : Injective H) :
    (hessianEquiv H hH : E →L[ℝ] E →L[ℝ] ℝ) = H := by
  ext v
  rfl

omit [FiniteDimensional ℝ E] in
/-- A positive velocity Hessian is injective. -/
theorem injective_of_pos (H : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ w : E, w ≠ 0 → 0 < H w w) :
    Injective H := by
  intro v w hvw
  by_contra hne
  have h := hpos (v - w) (sub_ne_zero.mpr hne)
  have h0 : H (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  rw [h0] at h
  simp at h

theorem velocityHessian_spray (L : E × E → ℝ) (z : E × E)
    (hH : Injective (velocityHessian L z)) :
    velocityHessian L z (spray L z) = positionTerm L z - mixedTerm L z := by
  unfold spray
  rw [← hessianEquiv_coe _ hH, ContinuousLinearMap.inverse_equiv]
  exact (hessianEquiv _ hH).apply_symm_apply _

omit [FiniteDimensional ℝ E] in
/-- Derivative of the velocity term along a jet curve: mixed term plus Hessian of the
acceleration. -/
theorem velocityTerm_fderiv_apply (L : E × E → ℝ) {z : E × E}
    (hL : ContDiffAt ℝ 2 L z) (a : E) :
    fderiv ℝ (velocityTerm L) z (z.2, a) =
      mixedTerm L z + velocityHessian L z a := by
  have hd : DifferentiableAt ℝ (velocityTerm L) z := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ L) z := hL.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun y => (fderiv ℝ L y).comp
        (ContinuousLinearMap.inr ℝ E E)) z := h1.clm_comp contDiffAt_const
    exact h2.differentiableAt (by norm_num)
  have hx : HasFDerivAt (fun y => velocityTerm L (y, z.2))
      ((fderiv ℝ (velocityTerm L) z).comp (ContinuousLinearMap.inl ℝ E E)) z.1 := by
    have h := hd.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
    simpa [Function.comp_def] using h
  have hv : HasFDerivAt (fun w => velocityTerm L (z.1, w))
      ((fderiv ℝ (velocityTerm L) z).comp (ContinuousLinearMap.inr ℝ E E)) z.2 := by
    have h := hd.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
    simpa [Function.comp_def] using h
  have hsplit : fderiv ℝ (velocityTerm L) z (z.2, a) =
      fderiv ℝ (velocityTerm L) z (z.2, 0) + fderiv ℝ (velocityTerm L) z (0, a) := by
    rw [← map_add]
    simp
  rw [hsplit]
  unfold mixedTerm velocityHessian
  rw [hx.fderiv, hv.fderiv]
  rfl

/-- A C² curve whose acceleration is the spray has vanishing Euler–Lagrange residual. -/
theorem residual_eq_zero_of_spray (L : E × E → ℝ) {x : ℝ → E} {t : ℝ}
    (hx : ContDiffAt ℝ 2 x t) (hL : ContDiffAt ℝ 2 L (curveJet x t))
    (hH : Injective (velocityHessian L (curveJet x t)))
    (hacc : deriv (deriv x) t = spray L (curveJet x t)) :
    residual L x t = 0 := by
  have hjet : HasDerivAt (curveJet x) (deriv x t, deriv (deriv x) t) t := by
    have h1 : HasDerivAt x (deriv x t) t :=
      (hx.differentiableAt (by norm_num)).hasDerivAt
    have h2 : HasDerivAt (deriv x) (deriv (deriv x) t) t := by
      have hd : ContDiffAt ℝ 1 (deriv x) t := hx.derivWithin (m := 1) (by norm_num)
      exact (hd.differentiableAt (by norm_num)).hasDerivAt
    exact h1.prodMk h2
  have hd : DifferentiableAt ℝ (velocityTerm L) (curveJet x t) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ L) (curveJet x t) := hL.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun y => (fderiv ℝ L y).comp
        (ContinuousLinearMap.inr ℝ E E)) (curveJet x t) := h1.clm_comp contDiffAt_const
    exact h2.differentiableAt (by norm_num)
  have hm : HasDerivAt (momentum L x)
      (fderiv ℝ (velocityTerm L) (curveJet x t) (deriv x t, deriv (deriv x) t)) t :=
    hd.hasFDerivAt.comp_hasDerivAt t hjet
  rw [Finsler.EulerCovariance.residual, hm.deriv]
  have hz : (curveJet x t).2 = deriv x t := rfl
  have := velocityTerm_fderiv_apply L hL (z := curveJet x t) (deriv (deriv x) t)
  rw [hz] at this
  rw [this, hacc, velocityHessian_spray L _ hH]
  abel


section Smooth

/-- Restriction of a functional on pairs to the velocity factor, as a continuous linear map. -/
def restrictVel : (E × E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip (ContinuousLinearMap.inr ℝ E E)

/-- Restriction of a functional on pairs to the position factor. -/
def restrictPos : (E × E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip (ContinuousLinearMap.inl ℝ E E)

omit [FiniteDimensional ℝ E] in
theorem velocityTerm_eq (L : E × E → ℝ) : velocityTerm L = fun z => restrictVel (fderiv ℝ L z) :=
  rfl

omit [FiniteDimensional ℝ E] in
theorem positionTerm_eq (L : E × E → ℝ) : positionTerm L = fun z => restrictPos (fderiv ℝ L z) :=
  rfl

omit [FiniteDimensional ℝ E] in
theorem velocityHessian_eq (L : E × E → ℝ) {z : E × E}
    (hd : DifferentiableAt ℝ (fderiv ℝ L) z) :
    velocityHessian L z =
      (restrictVel.comp (fderiv ℝ (fderiv ℝ L) z)).comp (ContinuousLinearMap.inr ℝ E E) := by
  have h1 : HasFDerivAt (fun w : E => (z.1, w)) (ContinuousLinearMap.inr ℝ E E) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have h2 : HasFDerivAt (fun w : E => fderiv ℝ L (z.1, w))
      ((fderiv ℝ (fderiv ℝ L) z).comp (ContinuousLinearMap.inr ℝ E E)) z.2 :=
    hd.hasFDerivAt.comp z.2 h1
  have h3 := restrictVel.hasFDerivAt.comp z.2 h2
  exact h3.fderiv

omit [FiniteDimensional ℝ E] in
theorem mixedTerm_eq (L : E × E → ℝ) {z : E × E} (hd : DifferentiableAt ℝ (fderiv ℝ L) z) :
    mixedTerm L z =
      ((restrictVel.comp (fderiv ℝ (fderiv ℝ L) z)).comp (ContinuousLinearMap.inl ℝ E E)) z.2 := by
  have h1 : HasFDerivAt (fun y : E => (y, z.2)) (ContinuousLinearMap.inl ℝ E E) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  have h2 : HasFDerivAt (fun y : E => fderiv ℝ L (y, z.2))
      ((fderiv ℝ (fderiv ℝ L) z).comp (ContinuousLinearMap.inl ℝ E E)) z.1 :=
    hd.hasFDerivAt.comp z.1 h1
  have h3' := (restrictVel (E := E)).hasFDerivAt.comp z.1 h2
  have h3 : HasFDerivAt (fun y : E => velocityTerm L (y, z.2))
      ((restrictVel.comp (fderiv ℝ (fderiv ℝ L) z)).comp (ContinuousLinearMap.inl ℝ E E)) z.1 :=
    h3'
  unfold mixedTerm
  rw [h3.fderiv]

/-- The spray is C^k where the Lagrangian is C^(k+2) and the velocity Hessian is injective. -/
theorem spray_contDiffAt (L : E × E → ℝ) {k : ℕ} {z : E × E} (hL : ContDiffAt ℝ (k + 2) L z)
    (hH : Injective (velocityHessian L z)) : ContDiffAt ℝ k (spray L) z := by
  have hfin : ((k : WithTop ℕ∞) + 2) ≠ ∞ := by
    have h : ((k : WithTop ℕ∞) + 2) = ((k + 2 : ℕ) : WithTop ℕ∞) := by push_cast; rfl
    rw [h]
    exact ENat.natCast_ne_coe_top (k + 2)
  have hev : ∀ᶠ z' in 𝓝 z, ContDiffAt ℝ (k + 2) L z' := hL.eventually hfin
  have hD2 : ContDiffAt ℝ k (fderiv ℝ (fderiv ℝ L)) z := by
    have h1 : ContDiffAt ℝ (k + 1) (fderiv ℝ L) z := hL.fderiv_right (m := k + 1) (by norm_cast)
    exact h1.fderiv_right (m := k) (by norm_cast)
  have hdiff : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ (fderiv ℝ L) z' := by
    filter_upwards [hev] with z' hz'
    have h1 : ContDiffAt ℝ (k + 1) (fderiv ℝ L) z' := hz'.fderiv_right (m := k + 1) (by norm_cast)
    exact h1.differentiableAt (by norm_cast)
  have hVH : ContDiffAt ℝ k (velocityHessian L) z := by
    have hc : ContDiffAt ℝ k (fun z' =>
        (restrictVel.comp (fderiv ℝ (fderiv ℝ L) z')).comp (ContinuousLinearMap.inr ℝ E E)) z :=
      (contDiffAt_const.clm_comp hD2).clm_comp contDiffAt_const
    exact hc.congr_of_eventuallyEq (by
      filter_upwards [hdiff] with z' hz'
      exact velocityHessian_eq L hz')
  have hMT : ContDiffAt ℝ k (mixedTerm L) z := by
    have hc : ContDiffAt ℝ k (fun z' =>
        ((restrictVel.comp (fderiv ℝ (fderiv ℝ L) z')).comp
          (ContinuousLinearMap.inl ℝ E E)) z'.2) z :=
      ((contDiffAt_const.clm_comp hD2).clm_comp contDiffAt_const).clm_apply contDiffAt_snd
    exact hc.congr_of_eventuallyEq (by
      filter_upwards [hdiff] with z' hz'
      exact mixedTerm_eq L hz')
  have hPT : ContDiffAt ℝ k (positionTerm L) z := by
    have h1 : ContDiffAt ℝ (k + 1) (fderiv ℝ L) z := hL.fderiv_right (m := k + 1) (by norm_cast)
    have h2 : ContDiffAt ℝ k (fderiv ℝ L) z := h1.of_le (by norm_cast; omega)
    rw [positionTerm_eq]
    exact contDiffAt_const.clm_apply h2
  have hinv : ContDiffAt ℝ k (fun z' => ContinuousLinearMap.inverse (velocityHessian L z')) z := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    have he := contDiffAt_map_inverse (𝕜 := ℝ) (n := k) (hessianEquiv _ hH)
    rw [hessianEquiv_coe] at he
    exact he.comp z hVH
  exact hinv.clm_apply (hPT.sub hMT)

end Smooth

section Homogeneous

variable {L : E × E → ℝ} (hhom : ∀ (y w : E) (r : ℝ), L (y, r • w) = r ^ 2 * L (y, w))
include hhom

omit [FiniteDimensional ℝ E] in
theorem positionTerm_smul {y w : E} (r : ℝ) (hd : DifferentiableAt ℝ L (y, w))
    (hdr : DifferentiableAt ℝ L (y, r • w)) :
    positionTerm L (y, r • w) = (r ^ 2) • positionTerm L (y, w) := by
  have h1 : HasFDerivAt (fun y' : E => L (y', r • w))
      ((fderiv ℝ L (y, r • w)).comp (ContinuousLinearMap.inl ℝ E E)) y :=
    hdr.hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y (r • w))
  have h2 : HasFDerivAt (fun y' : E => L (y', r • w))
      ((r ^ 2) • (fderiv ℝ L (y, w)).comp (ContinuousLinearMap.inl ℝ E E)) y := by
    have h := (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y w)).const_mul (r ^ 2)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun y' => hhom y' w r)
  exact h1.unique h2

omit [FiniteDimensional ℝ E] in
theorem velocityTerm_smul {y w : E} {r : ℝ} (hr : r ≠ 0) (hd : DifferentiableAt ℝ L (y, w))
    (hdr : DifferentiableAt ℝ L (y, r • w)) :
    velocityTerm L (y, r • w) = r • velocityTerm L (y, w) := by
  have hl : HasFDerivAt (fun w' : E => (y, r • w'))
      ((ContinuousLinearMap.inr ℝ E E).comp (r • ContinuousLinearMap.id ℝ E)) w := by
    have h := (hasFDerivAt_prodMk_right (𝕜 := ℝ) y (r • w)).comp w
      ((r • ContinuousLinearMap.id ℝ E).hasFDerivAt (x := w))
    simpa [Function.comp_def] using h
  have h1 : HasFDerivAt (fun w' : E => L (y, r • w'))
      ((fderiv ℝ L (y, r • w)).comp
        ((ContinuousLinearMap.inr ℝ E E).comp (r • ContinuousLinearMap.id ℝ E))) w :=
    hdr.hasFDerivAt.comp w hl
  have h2 : HasFDerivAt (fun w' : E => L (y, r • w'))
      ((r ^ 2) • (fderiv ℝ L (y, w)).comp (ContinuousLinearMap.inr ℝ E E)) w := by
    have h := (hd.hasFDerivAt.comp w (hasFDerivAt_prodMk_right (𝕜 := ℝ) y w)).const_mul (r ^ 2)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun w' => hhom y w' r)
  have heq := h1.unique h2
  ext k
  have hk := congrArg (fun T : E →L[ℝ] ℝ => T k) heq
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearMap.inr_apply] at hk
  change fderiv ℝ L (y, r • w) (0, k) = r * fderiv ℝ L (y, w) (0, k)
  have hk' : fderiv ℝ L (y, r • w) (0, r • k) = r * (r * fderiv ℝ L (y, w) (0, k)) := by
    rw [hk]
    ring
  have hlin : fderiv ℝ L (y, r • w) (0, r • k) = r * fderiv ℝ L (y, r • w) (0, k) := by
    rw [show ((0 : E), r • k) = r • ((0 : E), k) by simp, map_smul, smul_eq_mul]
  rw [hlin] at hk'
  exact mul_left_cancel₀ hr hk'

omit [FiniteDimensional ℝ E] in
theorem velocityHessian_smul {y w : E} {r : ℝ} (hr : r ≠ 0)
    (hdiff : ∀ w' : E, DifferentiableAt ℝ L (y, w'))
    (hv : DifferentiableAt ℝ (fun w' => velocityTerm L (y, w')) w)
    (hvr : DifferentiableAt ℝ (fun w' => velocityTerm L (y, w')) (r • w)) :
    velocityHessian L (y, r • w) = velocityHessian L (y, w) := by
  have hid : (fun w' : E => velocityTerm L (y, r • w')) =
      fun w' => r • velocityTerm L (y, w') :=
    funext fun w' => velocityTerm_smul hhom hr (hdiff w') (hdiff (r • w'))
  have h1 : HasFDerivAt (fun w' : E => velocityTerm L (y, r • w'))
      ((velocityHessian L (y, r • w)).comp (r • ContinuousLinearMap.id ℝ E)) w :=
    hvr.hasFDerivAt.comp w ((r • ContinuousLinearMap.id ℝ E).hasFDerivAt (x := w))
  have h2 : HasFDerivAt (fun w' : E => velocityTerm L (y, r • w'))
      (r • velocityHessian L (y, w)) w := by
    rw [hid]
    exact hv.hasFDerivAt.const_smul r
  have heq := h1.unique h2
  ext k
  have hk := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T k) heq
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul] at hk
  have hk2 := congrArg (fun T : E →L[ℝ] ℝ => r⁻¹ • T) hk
  simp only [smul_smul, inv_mul_cancel₀ hr, one_smul] at hk2
  exact congrArg (fun T : E →L[ℝ] ℝ => T _) hk2

omit [FiniteDimensional ℝ E] in
theorem mixedTerm_smul {U : Set E} (hU : IsOpen U) {y w : E} (hy : y ∈ U) {r : ℝ} (hr : r ≠ 0)
    (hdiff : ∀ y' ∈ U, ∀ w' : E, DifferentiableAt ℝ L (y', w'))
    (hm : DifferentiableAt ℝ (fun y' => velocityTerm L (y', w)) y) :
    mixedTerm L (y, r • w) = (r ^ 2) • mixedTerm L (y, w) := by
  have hev : (fun y' : E => velocityTerm L (y', r • w)) =ᶠ[𝓝 y]
      fun y' => r • velocityTerm L (y', w) := by
    filter_upwards [hU.mem_nhds hy] with y' hy'
    exact velocityTerm_smul hhom hr (hdiff y' hy' w) (hdiff y' hy' (r • w))
  unfold mixedTerm
  simp only
  have h5 : HasFDerivAt (fun y' => r • velocityTerm L (y', w))
      (r • fderiv ℝ (fun y' => velocityTerm L (y', w)) y) y := hm.hasFDerivAt.const_smul r
  rw [hev.fderiv_eq, h5.fderiv, smul_apply, map_smul, smul_smul, sq]

omit [FiniteDimensional ℝ E] in
theorem spray_smul {U : Set E} (hU : IsOpen U) {y w : E} (hy : y ∈ U) {r : ℝ} (hr : r ≠ 0)
    (hdiff : ∀ y' ∈ U, ∀ w' : E, DifferentiableAt ℝ L (y', w'))
    (hv : DifferentiableAt ℝ (fun w' => velocityTerm L (y, w')) w)
    (hvr : DifferentiableAt ℝ (fun w' => velocityTerm L (y, w')) (r • w))
    (hm : DifferentiableAt ℝ (fun y' => velocityTerm L (y', w)) y) :
    spray L (y, r • w) = (r ^ 2) • spray L (y, w) := by
  unfold spray
  rw [velocityHessian_smul hhom hr (hdiff y hy) hv hvr,
    positionTerm_smul hhom r (hdiff y hy w) (hdiff y hy (r • w)),
    mixedTerm_smul hhom hU hy hr hdiff hm]
  rw [show r ^ 2 • positionTerm L (y, w) - r ^ 2 • mixedTerm L (y, w) =
      r ^ 2 • (positionTerm L (y, w) - mixedTerm L (y, w)) from (smul_sub _ _ _).symm, map_smul]

end Homogeneous

end

end Finsler.LagrangianSpray
