module

public import Finsler.Geometry.RoundSplit
public import Finsler.Geometry.RoundQR

/-! The inverse of the chart and the split field on the ambient polygons.

On the polygons Q whose frequency-m coefficients are independent (Gram–Schmidt applies), the
inverse chart is (frame of the coefficients, triangular data minus (1, 0, 1), the rest of Q);
the chart inverts it, and conversely on pairs z ∈ V₂ with positive diagonal 1 + τ₁, 1 + τ₃. The
inverse chart is smooth there. The split field at Q is the image under the linear part of the
chart of the reflected fibre vector; along it the penalized energy decreases at the rate of the
split descent estimate. -/

@[expose] public section

namespace Finsler.RoundLabel

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon Finsler.RoundHessian
open Finsler.RoundModes Finsler.RoundNondeg Finsler.RoundCoords Finsler.RoundSpectral
open Finsler.RoundPenHess Finsler.RoundPenForm Finsler.AmbientPenalty Finsler.PolygonSmooth
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundQR
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)

/-! ### Smoothness of Gram–Schmidt -/

theorem contDiffAt_gsx {A : Ambient n} (hA : A ≠ 0) : ContDiffAt ℝ ∞ gsx A := by
  unfold gsx
  exact ((contDiffAt_id.norm ℝ hA).inv (norm_ne_zero_iff.mpr hA)).smul contDiffAt_id

theorem contDiffAt_res {A B : Ambient n} (hA : A ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : Ambient n × Ambient n => res p.1 p.2) (A, B) := by
  have hx : ContDiffAt ℝ ∞ (fun p : Ambient n × Ambient n => gsx p.1) (A, B) :=
    ContDiffAt.comp (g := gsx) (f := fun p : Ambient n × Ambient n => p.1) (A, B)
      (contDiffAt_gsx hA) contDiffAt_fst
  unfold res r12
  exact contDiffAt_snd.sub ((contDiffAt_snd.inner ℝ hx).smul hx)

/-- The Gram–Schmidt data are smooth at independent pairs. -/
theorem contDiffAt_gs {A B : Ambient n} (h : Indep A B) :
    ContDiffAt ℝ ∞ (fun p : Ambient n × Ambient n =>
      ((gsx p.1, gsu p.1 p.2), (‖p.1‖, r12 p.1 p.2, ‖res p.1 p.2‖))) (A, B) := by
  have hx : ContDiffAt ℝ ∞ (fun p : Ambient n × Ambient n => gsx p.1) (A, B) :=
    ContDiffAt.comp (g := gsx) (f := fun p : Ambient n × Ambient n => p.1) (A, B)
      (contDiffAt_gsx h.1) contDiffAt_fst
  have hr := contDiffAt_res (B := B) h.1
  have hu : ContDiffAt ℝ ∞ (fun p : Ambient n × Ambient n => gsu p.1 p.2) (A, B) := by
    unfold gsu
    exact ((hr.norm ℝ h.2).inv (norm_ne_zero_iff.mpr h.2)).smul hr
  have h12 : ContDiffAt ℝ ∞ (fun p : Ambient n × Ambient n => r12 p.1 p.2) (A, B) := by
    unfold r12
    exact contDiffAt_snd.inner ℝ hx
  exact (hx.prodMk hu).prodMk ((contDiffAt_fst.norm ℝ h.1).prodMk (h12.prodMk (hr.norm ℝ h.2)))

/-! ### The inverse chart -/

/-- The polygons with independent frequency-m coefficients form an open set. -/
theorem good_m_isOpen : IsOpen {Q : ZMod N → Ambient n | Good m Q} := by
  have hc : Continuous fun Q : ZMod N → Ambient n => (coefA m Q, coefB m Q) :=
    ((coefAL (n := n) (N := N) m).toContinuousLinearMap.continuous).prodMk
      ((coefBL (n := n) (N := N) m).toContinuousLinearMap.continuous)
  have hres : ∀ A B : Ambient n, A ≠ 0 →
      ContinuousAt (fun p : Ambient n × Ambient n => res p.1 p.2) (A, B) := fun A B hA =>
    (contDiffAt_res (B := B) hA).continuousAt
  rw [isOpen_iff_mem_nhds]
  intro Q hQ
  have h1 : ∀ᶠ P in 𝓝 Q, coefA m P ≠ 0 :=
    ((coefAL (n := n) (N := N) m).toContinuousLinearMap.continuous.continuousAt).eventually
      (isOpen_ne.mem_nhds hQ.1)
  have h2 : ∀ᶠ P in 𝓝 Q, res (coefA m P) (coefB m P) ≠ 0 := by
    have hca : ContinuousAt (fun P : ZMod N → Ambient n => res (coefA m P) (coefB m P)) Q :=
      ContinuousAt.comp (g := fun p : Ambient n × Ambient n => res p.1 p.2)
        (f := fun P => (coefA m P, coefB m P)) (hres _ _ hQ.1) hc.continuousAt
    exact hca.eventually (isOpen_ne.mem_nhds hQ.2)
  filter_upwards [h1, h2] with P hP1 hP2
  exact ⟨hP1, hP2⟩

/-- The inverse chart. -/
def unchart (Q : ZMod N → Ambient n) : (Ambient n × Ambient n) × Fib n N m :=
  (frameOf m Q, (((triOf m Q).1 - 1, (triOf m Q).2.1, (triOf m Q).2.2 - 1),
    ⟨Q - regPart m Q, rest_mem_kern hm hmN Q⟩))

/-- The chart in Gram–Schmidt form. -/
theorem chart_eq_build (p : (Ambient n × Ambient n) × Fib n N m) :
    chart m p = build m p.1 (1 + p.2.1.1, p.2.1.2.1, 1 + p.2.1.2.2) (p.2.2 : ZMod N → Ambient n) := by
  unfold chart build
  rw [lin_apply, ← add_assoc, ← regular_add]
  congr 2
  · rw [add_smul, one_smul]
  · rw [add_smul, one_smul]
    abel

theorem chart_unchart {Q : ZMod N → Ambient n} (hQ : Good m Q) : chart m (unchart hm hmN Q) = Q := by
  rw [chart_eq_build]
  change build m (frameOf m Q) (1 + ((triOf m Q).1 - 1), (triOf m Q).2.1,
    1 + ((triOf m Q).2.2 - 1)) (Q - regPart m Q) = Q
  rw [add_sub_cancel, add_sub_cancel]
  exact build_frameOf hQ

theorem unchart_chart {z : Ambient n × Ambient n} (hz : z ∈ V2) {ξ : Fib n N m}
    (h1 : 0 < 1 + ξ.1.1) (h3 : 0 < 1 + ξ.1.2.2) :
    Good m (chart m (z, ξ)) ∧ unchart hm hmN (chart m (z, ξ)) = (z, ξ) := by
  rw [chart_eq_build]
  obtain ⟨hg, hf, ht, hr⟩ := frameOf_build hm hmN hz.1 hz.2.1 hz.2.2 h1 h3 ξ.2.2
  refine ⟨hg, ?_⟩
  unfold unchart
  rw [hf, ht]
  refine Prod.ext rfl (Prod.ext ?_ (Subtype.ext hr))
  simp

theorem unchart_mem_V2 {Q : ZMod N → Ambient n} (hQ : Good m Q) : (unchart hm hmN Q).1 ∈ V2 :=
  frameOf_orthonormal hQ

/-- The inverse chart is smooth on the polygons with independent coefficients. -/
theorem unchart_contDiffAt {Q : ZMod N → Ambient n} (hQ : Good m Q) :
    ContDiffAt ℝ ∞ (unchart (n := n) (N := N) hm hmN) Q := by
  have hc : ContDiff ℝ ∞ fun Q : ZMod N → Ambient n => (coefA m Q, coefB m Q) :=
    ((coefAL (n := n) (N := N) m).toContinuousLinearMap.contDiff).prodMk
      ((coefBL (n := n) (N := N) m).toContinuousLinearMap.contDiff)
  have hgs := ContDiffAt.comp (g := fun p : Ambient n × Ambient n =>
      ((gsx p.1, gsu p.1 p.2), (‖p.1‖, r12 p.1 p.2, ‖res p.1 p.2‖)))
    (f := fun Q : ZMod N → Ambient n => (coefA m Q, coefB m Q)) Q (contDiffAt_gs hQ) hc.contDiffAt
  -- the rest as a linear map into the kernel
  let restL : (ZMod N → Ambient n) →ₗ[ℝ] kern (n := n) (N := N) m :=
    { toFun := fun Q => ⟨Q - regPart m Q, rest_mem_kern hm hmN Q⟩
      map_add' := fun Q Q' => Subtype.ext (by
        simp only [Submodule.coe_add, regPart, coefA_add, coefB_add, regular_add]
        abel)
      map_smul' := fun r Q => Subtype.ext (by
        simp only [Submodule.coe_smul, RingHom.id_apply, regPart, coefA_smul, coefB_smul,
          regular_smul, smul_sub]) }
  have hrest : ContDiff ℝ ∞ (fun Q : ZMod N → Ambient n =>
      (⟨Q - regPart m Q, rest_mem_kern hm hmN Q⟩ : kern (n := n) (N := N) m)) :=
    (LinearMap.toContinuousLinearMap restL).contDiff
  have htri : ContDiffAt ℝ ∞ (fun Q : ZMod N → Ambient n =>
      ((triOf m Q).1 - 1, (triOf m Q).2.1, (triOf m Q).2.2 - 1)) Q := by
    have h := contDiffAt_snd.comp Q hgs
    have h1 := (contDiffAt_fst.comp Q h).sub (contDiffAt_const (c := (1 : ℝ)))
    have h2 := contDiffAt_fst.comp Q (contDiffAt_snd.comp Q h)
    have h3 := (contDiffAt_snd.comp Q (contDiffAt_snd.comp Q h)).sub (contDiffAt_const (c := (1 : ℝ)))
    exact h1.prodMk (h2.prodMk h3)
  exact (contDiffAt_fst.comp Q hgs).prodMk (htri.prodMk hrest.contDiffAt)

end

end Finsler.RoundLabel
