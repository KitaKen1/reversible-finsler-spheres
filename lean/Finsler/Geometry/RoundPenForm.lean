module

public import Finsler.Geometry.RoundPenHess

/-! The second derivative of the penalized round energy at a regular m-gon.

For the regular m-gon Q of an orthonormal pair (x, u) and an increment

  B = (ρ_i Q_i) + (β_i t_i) + w,   t_i the unit tangents, w normal to the plane,

the second derivative of pen = E + log-penalty is

  D²pen(B, B) = 2N Σ (β_{i+1} − β_i)² + 2 Σ ρ_i² + D²E(w, w):

the radial part is invisible to E (vertex scaling invariance), in-plane and normal parts do
not interact (reflection symmetry), the tangential part gives the in-plane form, and the
penalty sees only the radial part. -/

@[expose] public section

namespace Finsler.RoundPenForm

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundEnergy Finsler.RoundPolygon
open Finsler.RoundHessian Finsler.RoundModes Finsler.RoundNondeg Finsler.PolygonSmooth
open Finsler.SphereRetraction Finsler.IndexComparison Finsler.AmbientPenalty
open Finsler.RoundPenHess
open Finset Filter Set
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ}

section Plane

variable {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
include hx hu hxu

/-- The unit tangents lie in the plane. -/
theorem tang_plane (i : ZMod N) :
    tang N m x u i = ⟪x, tang N m x u i⟫ • x + ⟪u, tang N m x u i⟫ • u := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪u, x⟫ = 0 := by rw [real_inner_comm, hxu]
  simp only [tang, circ, inner_add_right, real_inner_smul_right, hxx, huu, hxu, hux]
  simp

theorem inner_regular_tang (i : ZMod N) : ⟪regular N m x u i, tang N m x u i⟫ = 0 := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪u, x⟫ = 0 := by rw [real_inner_comm, hxu]
  simp only [regular, tang, circ, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hxx, huu, hxu, hux, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

omit hx hu hxu in
theorem plane_smul {v : Ambient n} (hv : v = ⟪x, v⟫ • x + ⟪u, v⟫ • u) (c : ℝ) :
    c • v = ⟪x, c • v⟫ • x + ⟪u, c • v⟫ • u := by
  rw [real_inner_smul_right, real_inner_smul_right, mul_smul, mul_smul, ← smul_add, ← hv]

omit hx hu hxu in
theorem inner_regular_normal {w : ZMod N → Ambient n} (hwx : ∀ i, ⟪x, w i⟫ = 0)
    (hwu : ∀ i, ⟪u, w i⟫ = 0) (i : ZMod N) : ⟪regular N m x u i, w i⟫ = 0 := by
  simp only [regular, circ, inner_add_left, real_inner_smul_left, hwx, hwu]
  ring

end Plane

variable (hm : 0 < m) (hmN : 2 * m < N) {x u : Ambient n}
  (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
include hm hmN hx hu hxu

theorem regular_unit : ∀ i, ‖regular N m x u i‖ = 1 := norm_regular hx hu hxu

theorem E_contDiffAt : ContDiffAt ℝ 2 (polyEnergyN (roundMetric n) N) (regular N m x u) :=
  (polyEnergyN_contDiffAt (regular_mem_good hm hmN hx hu hxu)).of_le (by simp)

theorem logPen_contDiffAt_regular : ContDiffAt ℝ 2 (logPen (n := n) (N := N)) (regular N m x u) :=
  (logPen_contDiffAt (regular_mem_good hm hmN hx hu hxu).1).of_le (by simp)

/-- The regular m-gons are critical for the penalized energy. -/
theorem fderiv_pen_regular : fderiv ℝ (pen (roundMetric n) N 1) (regular N m x u) = 0 := by
  have h1 := E_contDiffAt hm hmN hx hu hxu
  have h2 := logPen_contDiffAt_regular hm hmN hx hu hxu
  have hE := fderiv_regular_eq_zero hm hmN hx hu hxu (h1.differentiableAt (by simp))
  have hL := fderiv_logPen_unit (regular_unit hm hmN hx hu hxu)
  have hd : HasFDerivAt (pen (roundMetric n) N 1)
      (fderiv ℝ (polyEnergyN (roundMetric n) N) (regular N m x u) +
        (1 : ℝ) • fderiv ℝ (logPen (n := n) (N := N)) (regular N m x u)) (regular N m x u) :=
    (h1.differentiableAt (by simp)).hasFDerivAt.add
      ((h2.differentiableAt (by simp)).hasFDerivAt.const_mul 1)
  rw [hd.fderiv, hE, hL]
  simp

/-- The second derivative of the penalized energy is the sum of the second derivatives. -/
theorem pen_hessian_eq (v w : ZMod N → Ambient n) :
    fderiv ℝ (fderiv ℝ (pen (roundMetric n) N 1)) (regular N m x u) v w =
      fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u) v w +
        fderiv ℝ (fderiv ℝ (logPen (n := n) (N := N))) (regular N m x u) v w := by
  have hgood := regular_mem_good (n := n) hm hmN hx hu hxu
  have hev : fderiv ℝ (pen (roundMetric n) N 1) =ᶠ[𝓝 (regular N m x u)]
      fun P => fderiv ℝ (polyEnergyN (roundMetric n) N) P + fderiv ℝ (logPen (n := n) (N := N)) P := by
    filter_upwards [good_isOpen.mem_nhds hgood] with P hP
    have h1 := (polyEnergyN_contDiffAt hP).differentiableAt (by simp)
    have h2 := (logPen_contDiffAt (n := n) (N := N) hP.1).differentiableAt (by simp)
    have hd := h1.hasFDerivAt.add (h2.hasFDerivAt.const_mul 1)
    have hfun : pen (roundMetric n) N 1 = polyEnergyN (roundMetric n) N + fun y => 1 * logPen y := rfl
    rw [hfun, hd.fderiv, one_smul]
  have hE2 := E_contDiffAt hm hmN hx hu hxu
  have hL2 := logPen_contDiffAt_regular hm hmN hx hu hxu
  have hd1 : DifferentiableAt ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u) :=
    (hE2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ (logPen (n := n) (N := N))) (regular N m x u) :=
    (hL2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hev.fderiv_eq, (hd1.hasFDerivAt.fun_add hd2.hasFDerivAt).fderiv]
  rfl

/-- **The second derivative of the penalized energy at a regular m-gon.** -/
theorem pen_hessian_split (ρ β : ZMod N → ℝ) (w : ZMod N → Ambient n) (hwx : ∀ i, ⟪x, w i⟫ = 0)
    (hwu : ∀ i, ⟪u, w i⟫ = 0) :
    fderiv ℝ (fderiv ℝ (pen (roundMetric n) N 1)) (regular N m x u)
        (scaleL ρ (regular N m x u) + (fun i => β i • tang N m x u i) + w)
        (scaleL ρ (regular N m x u) + (fun i => β i • tang N m x u i) + w) =
      2 * (N * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2) + 2 * ∑ i : ZMod N, ρ i ^ 2 +
        fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u) w w := by
  set Q := regular N m x u with hQ
  set R := scaleL ρ Q with hR
  set T : ZMod N → Ambient n := fun i => β i • tang N m x u i with hT
  have hE2 := E_contDiffAt hm hmN hx hu hxu
  have hsym := hE2.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
  set H := fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) Q with hH
  -- the radial part is invisible to E
  have hrad : H R = 0 := hessian_radial_zero (fun c hc P => polyEnergyN_scaleVert _ c hc P) hE2
    (fderiv_regular_eq_zero hm hmN hx hu hxu (hE2.differentiableAt (by simp))) ρ
  -- in-plane and normal parts do not interact
  have hmix : H T w = 0 := hessian_mixed hm hmN hx hu hxu hE2 T w
    (fun i => plane_smul (tang_plane hx hu hxu i) (β i))
    (fun i => ⟨hwx i, hwu i⟩)
  have hE : H (R + T + w) (R + T + w) = H T T + H w w := by
    have hR1 : ∀ v, H R v = 0 := fun v => by rw [hrad]; rfl
    have hR2 : ∀ v, H v R = 0 := fun v => by rw [hsym.eq v R]; exact hR1 v
    have hTw : H w T = 0 := by rw [hsym.eq w T]; exact hmix
    simp only [map_add, ContinuousLinearMap.add_apply, hR1, hR2, hmix, hTw]
    ring
  have hTT : H T T = 2 * (N * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2) :=
    hessian_inplane hm hmN hx hu hxu hE2 β
  have hL : fderiv ℝ (fderiv ℝ (logPen (n := n) (N := N))) Q (R + T + w) (R + T + w) =
      2 * ∑ i : ZMod N, ρ i ^ 2 := by
    rw [logPen_hessian (regular_unit hm hmN hx hu hxu)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, hR, hT, scaleL_apply, inner_add_right, real_inner_smul_right]
    rw [inner_regular_tang hx hu hxu, inner_regular_normal hwx hwu,
      real_inner_self_eq_norm_sq, regular_unit hm hmN hx hu hxu]
    ring
  rw [pen_hessian_eq hm hmN hx hu hxu, hE, hTT, hL]
  ring

end

end Finsler.RoundPenForm
