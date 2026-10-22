module

public import Finsler.Geometry.RoundTransport
public import Finsler.Geometry.RoundDeform
public import Finsler.Geometry.LevelField
public import Finsler.Geometry.LevelCrossingFin

/-! The data of the crossing of the level (2πm)² of the penalized round polygon energy.

The label of the regular m-gons consists of

* the open set U = {Good, ‖ξ‖ < R₀} (ξ the fibre part of the inverse chart),
* the field W = fieldW (the push-forward of the model field (0, J z ξ)),
* the critical set C = {Good, ξ = 0} (the regular m-gons),
* the compact piece T = chart(V₂ × {sqF ≤ s_T}),
* the deformation β = χ ∘ unchart · (model ∘ unchart − pen) on the good polygons (zero elsewhere),
  χ the logarithmic cutoff of sqF with r² e^λ = s_T,
* the label sets 𝒲 = labO ρ and 𝒲' = labO ρ'.

Derivatives in the direction of the chart's linear part are derivatives along the fibre lines
of the chart, so the descent estimates of `RoundSplit` and `RoundDeform` give the descent
properties of W and of pen + β. -/

@[expose] public section

namespace Finsler.RoundLevel

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundCoords Finsler.RoundSpectral Finsler.RoundModes Finsler.AmbientPenalty
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundLabel Finsler.RoundModel Finsler.RoundQR
open Finsler.RoundCone Finsler.RoundThom Finsler.RoundModelLens Finsler.RoundTransport
open Finsler.RoundDeform Finsler.RoundPenHess Finsler.LogCutoff Finsler.PolygonSmooth
open Finsler.LevelField Finsler.LevelCrossingFin Finsler.LensFamily Finsler.PolygonDescent
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.EnergySphereSmooth
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LensContinuation Finsler.AmbientDescent Module
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ}

/-! ### Derivatives along the fibres of the chart -/

/-- The derivative in the direction of the chart's linear part is the derivative along the fibre
line. -/
theorem hasDerivAt_chart_line {f : (ZMod N → Ambient n) → ℝ} {z : Ambient n × Ambient n}
    {ξ : Fib n N m} (hf : DifferentiableAt ℝ f (chart m (z, ξ))) (v : Fib n N m) :
    HasDerivAt (fun t : ℝ => f (chart m (z, ξ + t • v)))
      (fderiv ℝ f (chart m (z, ξ)) (lin m z v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => chart m (z, ξ + t • v)) (lin m z v) 0 := by
    have e : (fun t : ℝ => chart m (z, ξ + t • v)) = fun t => chart m (z, ξ) + t • lin m z v := by
      funext t
      exact chart_line z ξ v t
    rw [e]
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (lin m z v)).const_add (chart m (z, ξ))
    rwa [one_smul] at h
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

/-- **Fibre derivatives through the chart.** -/
theorem fderiv_lin_eq {f : (ZMod N → Ambient n) → ℝ}
    {G : (Ambient n × Ambient n) × Fib n N m → ℝ} {z : Ambient n × Ambient n} {ξ : Fib n N m}
    (hf : DifferentiableAt ℝ f (chart m (z, ξ))) (hG : DifferentiableAt ℝ G (z, ξ)) (v : Fib n N m)
    (hfG : (fun t : ℝ => f (chart m (z, ξ + t • v))) =ᶠ[𝓝 0] fun t => G (z, ξ + t • v)) :
    fderiv ℝ f (chart m (z, ξ)) (lin m z v) = fderiv ℝ G (z, ξ) (0, v) :=
  ((hasDerivAt_chart_line hf v).congr_of_eventuallyEq hfG.symm).unique (hasDerivAt_fibre_line hG v)

theorem lin_contDiff :
    ContDiff ℝ ∞ fun p : (Ambient n × Ambient n) × Fib n N m => lin m p.1 p.2 := by
  rw [contDiff_pi]
  intro i
  have h : (fun p : (Ambient n × Ambient n) × Fib n N m => lin m p.1 p.2 i) = fun p =>
      Real.cos (2 * π * m / N * i.val) • (p.2.1.1 • p.1.1) +
        Real.sin (2 * π * m / N * i.val) • (p.2.1.2.1 • p.1.1 + p.2.1.2.2 • p.1.2) +
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) i := by
    funext p
    simp only [lin_apply, regular, circ, Pi.add_apply]
  rw [h]
  have hi : ContDiff ℝ ∞ (fun p : (Ambient n × Ambient n) × Fib n N m =>
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) i) :=
    (contDiff_apply ℝ (Ambient n) i).comp (fibV_contDiff (n := n) (N := N) (m := m))
  fun_prop

theorem linJ_contDiff (hm : 0 < m) (hmN : 2 * m < N) :
    ContDiff ℝ ∞ fun p : (Ambient n × Ambient n) × Fib n N m => lin m p.1 (J hm hmN p.1 p.2) := by
  have e : (fun p : (Ambient n × Ambient n) × Fib n N m => lin m p.1 (J hm hmN p.1 p.2)) =
      fun p => negP p - (lin m p.1 p.2 - negP p) := by
    funext p
    exact lin_J hm hmN p.1 p.2
  rw [e]
  exact (negP_contDiff (n := n) (N := N) (m := m)).sub
    ((lin_contDiff (n := n) (N := N) (m := m)).sub (negP_contDiff (n := n) (N := N) (m := m)))

variable (hm : 0 < m) (hmN : 2 * m < N)

theorem fieldW_contDiffAt {y : ZMod N → Ambient n} (hy : Good m y) :
    ContDiffAt ℝ ∞ (fieldW (n := n) (N := N) hm hmN) y :=
  ContDiffAt.comp (g := fun p : (Ambient n × Ambient n) × Fib n N m => lin m p.1 (J hm hmN p.1 p.2))
    (f := unchart hm hmN) y (linJ_contDiff hm hmN).contDiffAt (unchart_contDiffAt hm hmN hy)

/-- At chart points near the zero section the chart is inverted. -/
theorem chart_good {p : (Ambient n × Ambient n) × Fib n N m} (hp : p.1 ∈ V2) (hξ : ‖p.2‖ < 1) :
    Good m (chart m p) ∧ unchart hm hmN (chart m p) = p := by
  have h1 : ‖p.2.1.1‖ ≤ ‖p.2‖ := (norm_fst_le p.2.1).trans (norm_fst_le p.2)
  have h3 : ‖p.2.1.2.2‖ ≤ ‖p.2‖ :=
    ((norm_snd_le p.2.1.2).trans (norm_snd_le p.2.1)).trans (norm_fst_le p.2)
  rw [Real.norm_eq_abs] at h1 h3
  obtain ⟨hg, he⟩ := unchart_chart hm hmN (z := p.1) (ξ := p.2) hp
    (by linarith [neg_abs_le p.2.1.1]) (by linarith [neg_abs_le p.2.1.2.2])
  simp only [Prod.mk.eta] at hg he
  exact ⟨hg, he⟩

/-! ### The data of the label -/

/-- The open set of the label. -/
def Uset (R₀ : ℝ) : Set (ZMod N → Ambient n) := {y | Good m y ∧ ‖(unchart hm hmN y).2‖ < R₀}

/-- The critical set: the regular m-gons. -/
def Cset : Set (ZMod N → Ambient n) := {y | Good m y ∧ (unchart hm hmN y).2 = 0}

variable (m) in
/-- The compact piece. -/
def Tset (sT : ℝ) : Set (ZMod N → Ambient n) := chart m '' {p | p.1 ∈ V2 ∧ sqF p ≤ sT}

/-- The deformation. -/
def βf (r lam : ℝ) : (ZMod N → Ambient n) → ℝ :=
  Set.indicator {y | Good m y} fun y =>
    chi r lam (unchart hm hmN y) * (model m (unchart hm hmN y) - pen (roundMetric n) N 1 y)

theorem Uset_isOpen (R₀ : ℝ) : IsOpen (Uset (n := n) (N := N) hm hmN R₀) :=
  (unchart_continuousOn hm hmN).isOpen_inter_preimage (good_m_isOpen (m := m))
    (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)

theorem Cset_subset {R₀ : ℝ} (hR₀ : 0 < R₀) : Cset (n := n) (N := N) hm hmN ⊆ Uset hm hmN R₀ :=
  fun y hy => ⟨hy.1, by rw [hy.2, norm_zero]; exact hR₀⟩

section Constants

variable {R₀ : ℝ} (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ 1 / 2) {cF : ℝ} (hcF : 0 < cF)
  (hsqF : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, cF * ‖ξ‖ ^ 2 ≤ sqF (z, ξ))
  {sT : ℝ} (hsT : sT ≤ cF * R₀ ^ 2 / 4)

include hR₀ hcF hsqF hsT in
theorem norm_le_of_sqF {p : (Ambient n × Ambient n) × Fib n N m} (hp : p.1 ∈ V2)
    (hs : sqF p ≤ sT) : ‖p.2‖ ≤ R₀ / 2 := by
  have h := hsqF p.1 hp p.2
  have h2 : ‖p.2‖ ^ 2 ≤ (R₀ / 2) ^ 2 := by
    have : cF * ‖p.2‖ ^ 2 ≤ cF * (R₀ / 2) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hcF
  have hR : 0 ≤ R₀ / 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp h2

include hR₀ hcF hsqF hsT in
theorem Tset_isCompact : IsCompact (Tset (n := n) (N := N) m sT) := by
  have hsub : {p : (Ambient n × Ambient n) × Fib n N m | p.1 ∈ V2 ∧ sqF p ≤ sT} ⊆
      V2 ×ˢ closedBall (0 : Fib n N m) (R₀ / 2) := fun p hp =>
    ⟨hp.1, by rw [mem_closedBall, dist_zero_right]; exact norm_le_of_sqF hR₀ hcF hsqF hsT hp.1 hp.2⟩
  have hcl : IsClosed {p : (Ambient n × Ambient n) × Fib n N m | p.1 ∈ V2 ∧ sqF p ≤ sT} :=
    (isCompact_V2.isClosed.preimage continuous_fst).inter
      (isClosed_le (sqF_contDiff (n := n) (N := N) (m := m)).continuous continuous_const)
  exact ((isCompact_V2.prod (isCompact_closedBall _ _)).of_isClosed_subset hcl hsub).image
    (chart_contDiff (n := n) (N := N) m).continuous

include hR₀ hR₀1 hcF hsqF hsT in
/-- The points of the compact piece are inverted by the chart. -/
theorem mem_Tset {y : ZMod N → Ambient n} (hy : y ∈ Tset m sT) :
    Good m y ∧ unchart hm hmN y ∈ {p : (Ambient n × Ambient n) × Fib n N m | p.1 ∈ V2 ∧ sqF p ≤ sT} ∧
      ‖(unchart hm hmN y).2‖ ≤ R₀ / 2 ∧ chart m (unchart hm hmN y) = y := by
  obtain ⟨p, hp, rfl⟩ := hy
  have hξ := norm_le_of_sqF hR₀ hcF hsqF hsT hp.1 hp.2
  obtain ⟨hg, he⟩ := chart_good hm hmN hp.1 (by linarith)
  rw [he]
  exact ⟨hg, hp, hξ, rfl⟩

include hR₀ hR₀1 hcF hsqF hsT in
theorem Tset_subset : Tset m sT ⊆ Uset (n := n) (N := N) hm hmN R₀ := by
  intro y hy
  obtain ⟨hg, -, hξ, -⟩ := mem_Tset hm hmN hR₀ hR₀1 hcF hsqF hsT hy
  exact ⟨hg, by linarith⟩

end Constants

/-! ### Descent along the field -/

section Descent

variable {R₀ cS : ℝ} (hcS : 0 < cS)
  (hS : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ → (z, ξ) ∈ dom (n := n) (N := N) m ∧
    fderiv ℝ (Psi (n := n) (N := N) m) (z, ξ) (0, J hm hmN z ξ) ≤ -cS * ‖ξ‖ ^ 2)

include hS in
theorem Uset_good {y : ZMod N → Ambient n} (hy : y ∈ Uset hm hmN R₀) : y ∈ good N := by
  have h := (hS _ (unchart_mem_V2 hm hmN hy.1) _ hy.2.le).1
  change chart m ((unchart hm hmN y).1, (unchart hm hmN y).2) ∈ good N at h
  rwa [Prod.mk.eta, chart_unchart hm hmN hy.1] at h

include hS in
theorem Uset_reg : Uset hm hmN R₀ ⊆ regSet (roundMetric n) N 1 := fun y hy =>
  ⟨(Uset_good hm hmN hS hy).1, (pen_contDiffAt (Uset_good hm hmN hS hy) 1).of_le (by simp)⟩

include hS in
/-- The derivative of the penalized energy along W is the split derivative of Ψ. -/
theorem fderiv_pen_fieldW {y : ZMod N → Ambient n} (hy : y ∈ Uset hm hmN R₀) :
    fderiv ℝ (pen (roundMetric n) N 1) y (fieldW hm hmN y) =
      fderiv ℝ (Psi (n := n) (N := N) m) (unchart hm hmN y)
        (0, J hm hmN (unchart hm hmN y).1 (unchart hm hmN y).2) := by
  have hc : chart m ((unchart hm hmN y).1, (unchart hm hmN y).2) = y := chart_unchart hm hmN hy.1
  have hdom := (hS _ (unchart_mem_V2 hm hmN hy.1) _ hy.2.le).1
  have hGd : DifferentiableAt ℝ (Psi (n := n) (N := N) m)
      ((unchart hm hmN y).1, (unchart hm hmN y).2) :=
    ((Psi_contDiffOn (m := m)).contDiffAt (dom_isOpen.mem_nhds hdom)).differentiableAt (by simp)
  have hfd : DifferentiableAt ℝ (pen (roundMetric n) N 1)
      (chart m ((unchart hm hmN y).1, (unchart hm hmN y).2)) := by
    rw [hc]
    exact (pen_contDiffAt (Uset_good hm hmN hS hy) 1).differentiableAt (by simp)
  have h := fderiv_lin_eq hfd hGd (J hm hmN (unchart hm hmN y).1 (unchart hm hmN y).2)
    (Eventually.of_forall fun t => rfl)
  rw [hc] at h
  exact h

include hS in
theorem W_le {y : ZMod N → Ambient n} (hy : y ∈ Uset hm hmN R₀) :
    fderiv ℝ (pen (roundMetric n) N 1) y (fieldW hm hmN y) ≤ -cS * ‖(unchart hm hmN y).2‖ ^ 2 := by
  rw [fderiv_pen_fieldW hm hmN hS hy]
  have h := (hS _ (unchart_mem_V2 hm hmN hy.1) _ hy.2.le).2
  simp only [Prod.mk.eta] at h
  exact h

include hcS hS in
theorem W_nonpos {y : ZMod N → Ambient n} (hy : y ∈ Uset hm hmN R₀) :
    fderiv ℝ (pen (roundMetric n) N 1) y (fieldW hm hmN y) ≤ 0 := by
  have h := W_le hm hmN hS hy
  have : 0 ≤ cS * ‖(unchart hm hmN y).2‖ ^ 2 := by positivity
  linarith

include hcS hS in
theorem W_neg {y : ZMod N → Ambient n} (hy : y ∈ Uset hm hmN R₀) (hC : y ∉ Cset hm hmN) :
    fderiv ℝ (pen (roundMetric n) N 1) y (fieldW hm hmN y) < 0 := by
  have h := W_le hm hmN hS hy
  have hne : (unchart hm hmN y).2 ≠ 0 := fun h0 => hC ⟨hy.1, h0⟩
  have : 0 < cS * ‖(unchart hm hmN y).2‖ ^ 2 := by
    have := norm_pos_iff.mpr hne
    positivity
  linarith

end Descent

/-! ### The deformation -/

section Deform

variable {r lam sT : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) (hrs : r ^ 2 * Real.exp lam ≤ sT)

theorem βf_of_good {y : ZMod N → Ambient n} (hy : Good m y) :
    βf hm hmN r lam y = chi r lam (unchart hm hmN y) *
      (model m (unchart hm hmN y) - pen (roundMetric n) N 1 y) :=
  Set.indicator_of_mem (s := {y | Good m y}) hy _

theorem βf_of_not_good {y : ZMod N → Ambient n} (hy : ¬ Good m y) : βf hm hmN r lam y = 0 :=
  Set.indicator_of_notMem (s := {y | Good m y}) hy _

include hr hlam hrs in
theorem βf_eq_zero_of_not_mem {y : ZMod N → Ambient n} (hy : y ∉ Tset m sT) :
    βf hm hmN r lam y = 0 := by
  by_cases hg : Good m y
  · rw [βf_of_good hm hmN hg]
    have hχ : chi r lam (unchart hm hmN y) = 0 := by
      by_contra hne
      apply hy
      refine ⟨unchart hm hmN y, ⟨unchart_mem_V2 hm hmN hg, ?_⟩, chart_unchart hm hmN hg⟩
      by_contra hlt
      push_neg at hlt
      exact hne (chi_zero hr hlam (hrs.trans hlt.le))
    rw [hχ, zero_mul]
  · exact βf_of_not_good hm hmN hg

include hr hlam hrs in
theorem tsupport_βf_subset (hT : IsClosed (Tset (n := n) (N := N) m sT)) :
    tsupport (βf (n := n) (N := N) hm hmN r lam) ⊆ Tset m sT :=
  closure_minimal (fun y hy => by
    by_contra h
    exact hy (βf_eq_zero_of_not_mem hm hmN hr hlam hrs h)) hT

theorem βf_eventuallyEq {R₀ : ℝ} {y : ZMod N → Ambient n} (hy : y ∈ Uset hm hmN R₀) :
    βf hm hmN r lam =ᶠ[𝓝 y] fun y => chi r lam (unchart hm hmN y) *
      (model m (unchart hm hmN y) - pen (roundMetric n) N 1 y) := by
  filter_upwards [(Uset_isOpen hm hmN R₀).mem_nhds hy] with y' hy'
  exact βf_of_good hm hmN hy'.1

include hr hlam hrs in
theorem βf_differentiableAt {R₀ : ℝ} (hTU : Tset (n := n) (N := N) m sT ⊆ Uset hm hmN R₀)
    (hTc : IsClosed (Tset (n := n) (N := N) m sT))
    (hgood : ∀ y ∈ Uset (n := n) (N := N) hm hmN R₀, y ∈ good N)
    (y : ZMod N → Ambient n) : DifferentiableAt ℝ (βf hm hmN r lam) y := by
  by_cases hy : y ∈ Tset m sT
  · have hU := hTU hy
    have h1 : DifferentiableAt ℝ (fun y => chi r lam (unchart hm hmN y)) y :=
      (((chi_contDiff (n := n) (N := N) (m := m) hr hlam).contDiffAt).comp y
        (unchart_contDiffAt hm hmN hU.1)).differentiableAt (by simp)
    have h2 : DifferentiableAt ℝ (fun y => model m (unchart hm hmN y)) y :=
      (((model_contDiff (n := n) (N := N) (m := m)).contDiffAt).comp y
        (unchart_contDiffAt hm hmN hU.1)).differentiableAt (by simp)
    have h3 : DifferentiableAt ℝ (pen (roundMetric n) N 1) y :=
      (pen_contDiffAt (hgood y hU) 1).differentiableAt (by simp)
    exact (h1.mul (h2.sub h3)).congr_of_eventuallyEq (βf_eventuallyEq hm hmN hU)
  · have h0 : βf hm hmN r lam =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hTc.isOpen_compl.mem_nhds hy] with y' hy'
      exact βf_eq_zero_of_not_mem hm hmN hr hlam hrs hy'
    exact (differentiableAt_const 0).congr_of_eventuallyEq h0

include hr hlam hrs in
/-- The derivative of the deformed energy along W is the derivative of the deformation in the
chart. -/
theorem fderiv_penβ {R₀ : ℝ} (hR₀1 : R₀ < 1) (hTU : Tset (n := n) (N := N) m sT ⊆ Uset hm hmN R₀)
    (hTc : IsClosed (Tset (n := n) (N := N) m sT))
    (hgood : ∀ y ∈ Uset (n := n) (N := N) hm hmN R₀, y ∈ good N)
    {y : ZMod N → Ambient n} (hyT : y ∈ Tset m sT)
    (hdom : unchart hm hmN y ∈ dom (n := n) (N := N) m) :
    fderiv ℝ (fun y => pen (roundMetric n) N 1 y + βf hm hmN r lam y) y (fieldW hm hmN y) =
      fderiv ℝ (Gdef m r lam) (unchart hm hmN y)
        (0, J hm hmN (unchart hm hmN y).1 (unchart hm hmN y).2) := by
  have hU := hTU hyT
  set z := (unchart hm hmN y).1 with hz
  set ξ := (unchart hm hmN y).2 with hξ
  have hzV : z ∈ V2 := unchart_mem_V2 hm hmN hU.1
  have hc : chart m (z, ξ) = y := chart_unchart hm hmN hU.1
  have hzξ : (z, ξ) = unchart hm hmN y := Prod.mk.eta
  have hfd : DifferentiableAt ℝ (fun y => pen (roundMetric n) N 1 y + βf hm hmN r lam y)
      (chart m (z, ξ)) := by
    rw [hc]
    exact ((pen_contDiffAt (hgood y hU) 1).differentiableAt (by simp)).add
      (βf_differentiableAt hm hmN hr hlam hrs hTU hTc hgood y)
  have hGd : DifferentiableAt ℝ (Gdef m r lam) (z, ξ) := by
    have hΨ : DifferentiableAt ℝ (Psi (n := n) (N := N) m) (z, ξ) := by
      rw [hzξ]
      exact ((Psi_contDiffOn (m := m)).contDiffAt (dom_isOpen.mem_nhds hdom)).differentiableAt
        (by simp)
    have hχ := (chi_contDiff (n := n) (N := N) (m := m) hr hlam).differentiable (by simp) (z, ξ)
    have hM := (model_contDiff (n := n) (N := N) (m := m)).differentiable (by simp) (z, ξ)
    exact hΨ.add (hχ.mul (hM.sub hΨ))
  have hev : (fun t : ℝ => pen (roundMetric n) N 1 (chart m (z, ξ + t • J hm hmN z ξ)) +
      βf hm hmN r lam (chart m (z, ξ + t • J hm hmN z ξ))) =ᶠ[𝓝 0]
      fun t => Gdef m r lam (z, ξ + t • J hm hmN z ξ) := by
    have hξ1 : ‖ξ‖ < 1 := by
      have := hU.2
      rw [← hξ] at this
      linarith
    have hcont : ContinuousAt (fun t : ℝ => ‖ξ + t • J hm hmN z ξ‖) 0 := by fun_prop
    filter_upwards [hcont.eventually (gt_mem_nhds (show ‖ξ + (0 : ℝ) • J hm hmN z ξ‖ < 1 by
      simpa using hξ1))] with t ht
    obtain ⟨hg, he⟩ := chart_good hm hmN (p := (z, ξ + t • J hm hmN z ξ)) hzV ht
    rw [βf_of_good hm hmN hg, he]
    rfl
  have h := fderiv_lin_eq hfd hGd (J hm hmN z ξ) hev
  rw [hc] at h
  rw [← hzξ]
  exact h

end Deform

/-! ### Values -/

theorem negP_zero (z : Ambient n × Ambient n) : negP (z, (0 : Fib n N m)) = 0 := by
  have h := negV_smul (m := m) (N := N) z 0 (0 : ZMod N → Ambient n)
  rw [zero_smul, zero_smul] at h
  change negV m z (((0 : Fib n N m).2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) = 0
  simp only [Prod.snd_zero, Submodule.coe_zero]
  exact h

theorem sqN_zero (z : Ambient n × Ambient n) : sqN (z, (0 : Fib n N m)) = 0 := by
  unfold sqN
  rw [negP_zero]
  simp [pair]

theorem sqP_zero (z : Ambient n × Ambient n) : sqP (z, (0 : Fib n N m)) = 0 := by
  unfold sqP
  rw [negP_zero]
  simp [pair]

theorem model_zero (z : Ambient n × Ambient n) :
    model m (z, (0 : Fib n N m)) = (2 * π * m) ^ 2 := by
  unfold model
  rw [sqN_zero, sqP_zero]
  ring

section Values

variable {R₀ : ℝ} (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ 1 / 2) {cF : ℝ} (hcF : 0 < cF)
  (hsqF : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, cF * ‖ξ‖ ^ 2 ≤ sqF (z, ξ))
  {sT : ℝ} (hsT : sT ≤ cF * R₀ ^ 2 / 4) {C_Q : ℝ} (hCQ : 0 ≤ C_Q)
  (hQ : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ →
    |Psi (n := n) (N := N) m (z, ξ) - (2 * π * m) ^ 2| ≤ C_Q * ‖ξ‖ ^ 2)

theorem pen_eq_Psi {y : ZMod N → Ambient n} (hy : Good m y) :
    pen (roundMetric n) N 1 y = Psi (n := n) (N := N) m (unchart hm hmN y) := by
  change _ = pen (roundMetric n) N 1 (chart m (unchart hm hmN y))
  rw [chart_unchart hm hmN hy]

include hR₀ hQ in
/-- The values on the critical set. -/
theorem Cset_val {y : ZMod N → Ambient n} (hy : y ∈ Cset hm hmN) (r lam : ℝ) :
    pen (roundMetric n) N 1 y = (2 * π * m) ^ 2 ∧ βf hm hmN r lam y = 0 := by
  have hu : unchart hm hmN y = ((unchart hm hmN y).1, 0) := Prod.ext rfl hy.2
  have hz := unchart_mem_V2 hm hmN hy.1
  have hq := hQ _ hz (0 : Fib n N m) (by rw [norm_zero]; exact hR₀.le)
  rw [norm_zero, zero_pow two_ne_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at hq
  have hpen : pen (roundMetric n) N 1 y = (2 * π * m) ^ 2 := by
    rw [pen_eq_Psi hm hmN hy.1, hu, hq]
  refine ⟨hpen, ?_⟩
  rw [βf_of_good hm hmN hy.1, hpen, hu, model_zero, sub_self, mul_zero]

variable {r lam : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) (hrs : r ^ 2 * Real.exp lam ≤ sT)
  {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
  (hMΨ : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ →
    |model m (z, ξ) - Psi (n := n) (N := N) m (z, ξ)| ≤ C₁ * sqF (z, ξ))

include hR₀ hR₀1 hcF hsqF hsT hr hlam hrs hC₁ hMΨ in
/-- The deformation is bounded by η = C₁ s_T. -/
theorem βf_bound (y : ZMod N → Ambient n) : |βf hm hmN r lam y| ≤ C₁ * sT := by
  have hsT0 : 0 ≤ sT := (by positivity : (0 : ℝ) ≤ r ^ 2 * Real.exp lam).trans hrs
  by_cases hT : y ∈ Tset m sT
  · obtain ⟨hg, ⟨hz, hsq⟩, hξ, -⟩ := mem_Tset hm hmN hR₀ hR₀1 hcF hsqF hsT hT
    rw [βf_of_good hm hmN hg, abs_mul]
    have h1 : |chi r lam (unchart hm hmN y)| ≤ 1 := by
      unfold chi
      rw [abs_of_nonneg (logCut_nonneg _ _ _)]
      exact logCut_le_one _ _ _
    have h2 : |model m (unchart hm hmN y) - pen (roundMetric n) N 1 y| ≤ C₁ * sT := by
      have h := hMΨ _ hz _ (hξ.trans (by linarith))
      simp only [Prod.mk.eta] at h
      rw [pen_eq_Psi hm hmN hg]
      exact h.trans (mul_le_mul_of_nonneg_left hsq hC₁)
    calc |chi r lam (unchart hm hmN y)| * |model m (unchart hm hmN y) - pen (roundMetric n) N 1 y|
        ≤ 1 * (C₁ * sT) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = C₁ * sT := one_mul _
  · rw [βf_eq_zero_of_not_mem hm hmN hr hlam hrs hT, abs_zero]
    positivity

include hm hmN hR₀ hR₀1 hcF hsqF hsT hCQ hQ in
/-- The penalized energy on the compact piece lies in the strip. -/
theorem Tset_val {a b η : ℝ} (hη : C_Q / cF * sT + η < (2 * π * m) ^ 2 - a)
    (hη' : C_Q / cF * sT + η < b - (2 * π * m) ^ 2) {y : ZMod N → Ambient n}
    (hy : y ∈ Tset m sT) :
    a + η < pen (roundMetric n) N 1 y ∧ pen (roundMetric n) N 1 y < b - η := by
  obtain ⟨hg, ⟨hz, hsq⟩, hξ, -⟩ := mem_Tset hm hmN hR₀ hR₀1 hcF hsqF hsT hy
  have hq := hQ _ hz _ (hξ.trans (by linarith))
  simp only [Prod.mk.eta] at hq
  have h1 : C_Q * ‖(unchart hm hmN y).2‖ ^ 2 ≤ C_Q / cF * sT := by
    have h := hsqF _ hz (unchart hm hmN y).2
    simp only [Prod.mk.eta] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hcF]
    nlinarith
  rw [pen_eq_Psi hm hmN hg]
  rw [abs_le] at hq
  constructor <;> linarith

end Values

/-! ### The label sets -/

section Labels

theorem labA_sub_Tset {ρ sT : ℝ} (hρs : 2 * ρ ^ 2 ≤ sT) :
    labA (n := n) (N := N) hm hmN ρ ⊆ Tset m sT := fun y hy =>
  ⟨unchart hm hmN y, ⟨unchart_mem_V2 hm hmN hy.1, by unfold sqF; linarith [hy.2.1, hy.2.2]⟩,
    chart_unchart hm hmN hy.1⟩

theorem Cset_sub_labO {ρ' : ℝ} (hρ' : 0 < ρ') (Q : Om n N) (hQ : Q.1 ∈ Cset hm hmN) :
    Q ∈ labO hm hmN ρ' := by
  have hu : unchart hm hmN Q.1 = ((unchart hm hmN Q.1).1, 0) := Prod.ext rfl hQ.2
  refine ⟨hQ.1, ?_, ?_⟩
  · rw [hu, sqN_zero]
    positivity
  · rw [hu, sqP_zero]
    positivity

theorem small_of {R₀ cS cF sT ρ : ℝ} (hR₀ : 0 < R₀) (hcF : 0 < cF)
    (hsqF : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, cF * ‖ξ‖ ^ 2 ≤ sqF (z, ξ))
    (hsT : sT ≤ cF * R₀ ^ 2 / 4)
    (hS : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ → (z, ξ) ∈ dom (n := n) (N := N) m ∧
      fderiv ℝ (Psi (n := n) (N := N) m) (z, ξ) (0, J hm hmN z ξ) ≤ -cS * ‖ξ‖ ^ 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρs : 2 * ρ ^ 2 ≤ sT) : Small n N m ρ := by
  refine ⟨hρ0, hρ1, fun p hp hN hP j => ?_⟩
  have hs : sqF p ≤ sT := by unfold sqF; linarith
  have hξ := norm_le_of_sqF hR₀ hcF hsqF hsT hp hs
  have h := (hS p.1 hp p.2 (by linarith)).1
  exact h.1 j

theorem penβ_labA {ρ r lam : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) (hρr : 2 * ρ ^ 2 ≤ r ^ 2)
    {Q : ZMod N → Ambient n} (hQ : Q ∈ labA hm hmN ρ) :
    pen (roundMetric n) N 1 Q + βf hm hmN r lam Q = model m (unchart hm hmN Q) := by
  rw [βf_of_good hm hmN hQ.1]
  have hs : sqF (unchart hm hmN Q) ≤ r ^ 2 := by unfold sqF; linarith [hQ.2.1, hQ.2.2]
  rw [chi_one hr hlam hs]
  ring

end Labels

/-! ### The critical polygons of the band -/

/-- The critical polygons with energy between the cuts around (2πm)² are regular m-gons, which
lie in the compact piece. -/
theorem crit_mem_Tset {δ : ℝ} (hδ2 : δ ≤ 2) {a b : ℝ} (ha : 0 < a)
    (hlo : (2 * π * ((m : ℝ) - 1)) ^ 2 < a) (hhi : b < (2 * π * ((m : ℝ) + 1)) ^ 2) {sT : ℝ}
    (hsT : 0 ≤ sT) (q : ZMod N → Sphere n)
    (hq1 : a ≤ PolygonDescent.energy (roundMetric n) N q)
    (hq2 : PolygonDescent.energy (roundMetric n) N q ≤ b) (hshort : ShortPolygon δ q)
    (hc : PolyCritical (roundMetric n) N q) : (incl q : Om n N).1 ∈ Tset m sT := by
  have hna : ∀ i : ZMod N, ⟪(q i : Ambient n), q (i + 1)⟫ ≠ -1 := by
    intro i h
    have h1 := hshort i
    have h2 : ‖(q (i + 1) : Ambient n) - q i‖ ^ 2 = 4 := by
      rw [norm_sub_sq_real, real_inner_comm, h]
      simp
      norm_num
    have h3 : ‖(q (i + 1) : Ambient n) - q i‖ = 2 := by
      have h0 := norm_nonneg ((q (i + 1) : Ambient n) - q i)
      nlinarith
    linarith
  have hpos : 0 < polyEnergy (roundMetric n) N (fun i => (q i : Ambient n)) :=
    ha.trans_le hq1
  obtain ⟨x, u, m', hx, hu, hxu, hm', hm'N, hq⟩ := regular_of_polyCritical hna hc hpos
  have hreg : (fun i => (q i : Ambient n)) = regular N m' x u := by
    funext i
    have h := hq i.val
    rw [ZMod.natCast_zmod_val] at h
    rw [h, ← ZMod.natCast_zmod_val i, regular_natCast, ZMod.natCast_zmod_val]
    rfl
  have hE : PolygonDescent.energy (roundMetric n) N q = (2 * π * m') ^ 2 := by
    change polyEnergy (roundMetric n) N (fun i => (q i : Ambient n)) = _
    rw [hreg, polyEnergy_regular hm'N hx hu hxu]
  rw [hE] at hq1 hq2
  have hπ : 0 < π := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'
  have hmm : m' = m := by
    have h1 : 2 * π * ((m : ℝ) - 1) < 2 * π * m' := by
      by_cases hm0 : (m : ℝ) - 1 ≤ 0
      · nlinarith
      · push_neg at hm0
        exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp
          (hlo.trans_le hq1)
    have h2 : 2 * π * m' < 2 * π * ((m : ℝ) + 1) :=
      (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp (hq2.trans_lt hhi)
    have h1' : (m : ℝ) - 1 < m' := lt_of_mul_lt_mul_left h1 (by positivity)
    have h2' : (m' : ℝ) < m + 1 := lt_of_mul_lt_mul_left h2 (by positivity)
    have e1 : m < m' + 1 := by exact_mod_cast (show (m : ℝ) < m' + 1 by linarith)
    have e2 : m' < m + 1 := by exact_mod_cast h2'
    omega
  subst hmm
  refine ⟨((x, u), 0), ⟨⟨hx, hu, hxu⟩, ?_⟩, ?_⟩
  · unfold sqF
    rw [sqN_zero, sqP_zero, add_zero]
    exact hsT
  · rw [chart_zero]
    exact hreg.symm

/-! ### The crossing of the level -/

set_option maxHeartbeats 1600000 in
/-- **The crossing of the level (2πm)² of the penalized round polygon energy.** For odd N = 2M + 1
with m < M, cuts a < (2πm)² < b with no other critical value of the polygon energy between them,
polygons of energy at most b short, and V₂ finite dimensional in every degree, the crossing pair
of the penalized energy is finite dimensional in every degree with the dimensions of V₂ shifted by
(2m − 1)(n − 1). -/
theorem round_level (hn : 1 ≤ n) {M : ℕ} (hNM : N = 2 * M + 1) (hm : 0 < m) (hmM : m < M)
    {δ : ℝ} (hδ2 : δ ≤ 2)
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy (roundMetric n)) ((P : Ambient n), (Q : Ambient n)))
    {a b : ℝ} (ha : 0 < a) (hlo : (2 * π * ((m : ℝ) - 1)) ^ 2 < a) (hac : a < (2 * π * m) ^ 2)
    (hcb : (2 * π * m) ^ 2 < b) (hhi : b < (2 * π * ((m : ℝ) + 1)) ^ 2)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy (roundMetric n) N q ≤ b →
      ShortPolygon δ q)
    (hV2 : ∀ k, Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k))
    (hab : a ≤ b) (q : ℕ) :
    Module.Finite (ZMod 2) (crossH (penW (roundMetric n) N 1) hab q) ∧
      finrank (ZMod 2) (crossH (penW (roundMetric n) N 1) hab q) =
        if (2 * m - 1) * (n - 1) ≤ q then
          finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ)))
            (q - (2 * m - 1) * (n - 1)))
        else 0 := by
  have hmN := two_m_lt_N hNM hmM
  obtain ⟨R_S, cS, hRS, hcS, hS⟩ := exists_split_descent (n := n) hNM hm hmM
  obtain ⟨R_D, cD, lam, hRD, hcD, hlam, hD⟩ := exists_deform_descent (n := n) hNM hm hmM
  obtain ⟨R_Q, C_Q, hRQ, hCQ, hQ⟩ := exists_quadratic (n := n) hNM hm hmM
  obtain ⟨cF, CF, hcF, hCF, hF⟩ := exists_sqF_bounds (n := n) (N := N) (m := m)
  -- the radius
  set R₀ := min (min R_S R_D) (min R_Q (1 / 2)) with hR₀def
  have hR₀ : 0 < R₀ := lt_min (lt_min hRS hRD) (lt_min hRQ (by norm_num))
  have hR₀1 : R₀ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hR₀S : R₀ ≤ R_S := (min_le_left _ _).trans (min_le_left _ _)
  have hR₀D : R₀ ≤ R_D := (min_le_left _ _).trans (min_le_right _ _)
  have hR₀Q : R₀ ≤ R_Q := (min_le_right _ _).trans (min_le_left _ _)
  have hS' : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ → (z, ξ) ∈ dom (n := n) (N := N) m ∧
      fderiv ℝ (Psi (n := n) (N := N) m) (z, ξ) (0, J hm hmN z ξ) ≤ -cS * ‖ξ‖ ^ 2 :=
    fun z hz ξ hξ => hS z hz ξ (hξ.trans hR₀S)
  have hQ' : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ →
      |Psi (n := n) (N := N) m (z, ξ) - (2 * π * m) ^ 2| ≤ C_Q * ‖ξ‖ ^ 2 :=
    fun z hz ξ hξ => (hQ z hz ξ (hξ.trans hR₀Q)).2
  have hsqF : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, cF * ‖ξ‖ ^ 2 ≤ sqF (z, ξ) :=
    fun z hz ξ => (hF z hz ξ).1
  -- the comparison of the model with Ψ
  set C₁ := 1 + C_Q / cF with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hMΨ : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ →
      |model m (z, ξ) - Psi (n := n) (N := N) m (z, ξ)| ≤ C₁ * sqF (z, ξ) := by
    intro z hz ξ hξ
    have h1 : |model m (z, ξ) - (2 * π * m) ^ 2| ≤ sqF (z, ξ) := by
      unfold model sqF
      rw [show (2 * π * m) ^ 2 - sqN (z, ξ) + sqP (z, ξ) - (2 * π * m) ^ 2 =
        sqP (z, ξ) - sqN (z, ξ) by ring, abs_le]
      have := sqN_nonneg (z, ξ)
      have := sqP_nonneg (z, ξ)
      constructor <;> linarith
    have h2 : C_Q * ‖ξ‖ ^ 2 ≤ C_Q / cF * sqF (z, ξ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcF]
      nlinarith [hsqF z hz ξ]
    have hq := hQ' z hz ξ hξ
    calc |model m (z, ξ) - Psi (n := n) (N := N) m (z, ξ)|
        = |(model m (z, ξ) - (2 * π * m) ^ 2) - (Psi m (z, ξ) - (2 * π * m) ^ 2)| := by ring_nf
      _ ≤ |model m (z, ξ) - (2 * π * m) ^ 2| + |Psi m (z, ξ) - (2 * π * m) ^ 2| := abs_sub _ _
      _ ≤ sqF (z, ξ) + C_Q / cF * sqF (z, ξ) := add_le_add h1 (hq.trans h2)
      _ = C₁ * sqF (z, ξ) := by rw [hC₁def]; ring
  -- the size of the piece
  set δw := min ((2 * π * m) ^ 2 - a) (b - (2 * π * m) ^ 2) with hδwdef
  have hδw : 0 < δw := lt_min (by linarith) (by linarith)
  set sT := min (cF * R₀ ^ 2 / 4) (δw / (2 * (C_Q / cF + C₁ + 1))) with hsTdef
  have hsT0 : 0 < sT := lt_min (by positivity) (by positivity)
  have hsT : sT ≤ cF * R₀ ^ 2 / 4 := min_le_left _ _
  have hsTw : (C_Q / cF + C₁) * sT < δw := by
    have h1 : sT ≤ δw / (2 * (C_Q / cF + C₁ + 1)) := min_le_right _ _
    have h2 : 0 ≤ C_Q / cF := by positivity
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hη : C_Q / cF * sT + C₁ * sT < (2 * π * m) ^ 2 - a := by
    have := min_le_left ((2 * π * m) ^ 2 - a) (b - (2 * π * m) ^ 2)
    nlinarith
  have hη' : C_Q / cF * sT + C₁ * sT < b - (2 * π * m) ^ 2 := by
    have := min_le_right ((2 * π * m) ^ 2 - a) (b - (2 * π * m) ^ 2)
    nlinarith
  -- the cutoff radius
  set r := Real.sqrt (sT * Real.exp (-lam)) with hrdef
  have hr2 : r ^ 2 = sT * Real.exp (-lam) := Real.sq_sqrt (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr : r ≠ 0 := hr0.ne'
  have hrs : r ^ 2 * Real.exp lam ≤ sT := by
    rw [hr2, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hr2s : r ^ 2 ≤ sT := by
    rw [hr2]
    exact mul_le_of_le_one_right hsT0.le (Real.exp_le_one_iff.mpr (by linarith))
  -- the label radii
  set ρ := min 1 (r / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρr : 2 * ρ ^ 2 ≤ r ^ 2 := by
    have h : ρ ≤ r / 2 := min_le_right _ _
    have h' : ρ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ hρ0.le h 2
    nlinarith
  have hρs : 2 * ρ ^ 2 ≤ sT := hρr.trans hr2s
  set ρ' := ρ / Real.exp 1 with hρ'def
  have hρ'0 : 0 < ρ' := div_pos hρ0 (Real.exp_pos 1)
  have hρρ' : Real.exp 1 * ρ' ≤ ρ := by
    rw [hρ'def, mul_div_cancel₀ _ (Real.exp_pos 1).ne']
  have hsmall : Small n N m ρ := small_of hm hmN hR₀ hcF hsqF hsT hS' hρ0 hρ1 hρs
  -- the compact piece
  have hTc : IsCompact (Tset (n := n) (N := N) m sT) := Tset_isCompact hR₀ hcF hsqF hsT
  have hTU : Tset (n := n) (N := N) m sT ⊆ Uset hm hmN R₀ :=
    Tset_subset hm hmN hR₀ hR₀1 hcF hsqF hsT
  have hgood : ∀ y ∈ Uset (n := n) (N := N) hm hmN R₀, y ∈ good N :=
    fun y hy => Uset_good hm hmN hS' hy
  -- the descent of the deformed energy on the piece
  have hβ : ∀ y ∈ tsupport (βf (n := n) (N := N) hm hmN r lam),
      fderiv ℝ (fun y => pen (roundMetric n) N 1 y + βf hm hmN r lam y) y (fieldW hm hmN y) ≤
        -cD * sqF (unchart hm hmN y) := by
    intro y hy
    have hyT := tsupport_βf_subset hm hmN hr hlam hrs hTc.isClosed hy
    obtain ⟨hg, ⟨hz, hsq⟩, hξ, -⟩ := mem_Tset hm hmN hR₀ hR₀1 hcF hsqF hsT hyT
    have hξD : ‖(unchart hm hmN y).2‖ ≤ R_D := hξ.trans (by linarith)
    obtain ⟨hdom, -, hG⟩ := hD r lam hr le_rfl _ hz _ hξD
    simp only [Prod.mk.eta] at hdom hG
    rw [fderiv_penβ hm hmN hr hlam hrs (by linarith) hTU hTc.isClosed hgood hyT hdom]
    exact hG
  -- the crossing of the level
  obtain ⟨d, hd, hcross⟩ := level_crossing_fin (roundMetric n) hn hδ (a₀ := a) (b₀ := b) hshort
    (s := (Finset.univ : Finset Unit)) (U := fun _ => Uset hm hmN R₀)
    (W := fun _ => fieldW hm hmN) (β := fun _ => βf hm hmN r lam) (C := fun _ => Cset hm hmN)
    (T := fun _ => Tset m sT) (𝒲 := fun _ => labO hm hmN ρ) (𝒲' := fun _ => labO hm hmN ρ')
    (fun _ _ => Uset_isOpen hm hmN R₀) (fun _ _ => Uset_reg hm hmN hS')
    (fun i _ j _ hij => absurd (Subsingleton.elim i j) hij)
    (fun _ _ y hy => (fieldW_contDiffAt hm hmN hy.1).contDiffWithinAt)
    (fun _ _ y hy => W_nonpos hm hmN hcS hS' hy) (fun _ _ y hy hC => W_neg hm hmN hcS hS' hy hC)
    (fun _ _ => hTc) (fun _ _ => hTU) (fun _ _ => tsupport_βf_subset hm hmN hr hlam hrs hTc.isClosed)
    (fun _ _ y => βf_differentiableAt hm hmN hr hlam hrs hTU hTc.isClosed hgood y)
    (fun _ _ y hy => (hβ y hy).trans (by
      have := sqF_nonneg (unchart hm hmN y)
      nlinarith))
    (fun _ _ y hy hC => (hβ y hy).trans_lt (by
      have hyT := tsupport_βf_subset hm hmN hr hlam hrs hTc.isClosed hy
      have hg := (hTU hyT).1
      have hne : (unchart hm hmN y).2 ≠ 0 := fun h0 => hC ⟨hg, h0⟩
      have hpos : 0 < sqF ((unchart hm hmN y).1, (unchart hm hmN y).2) := sqF_pos _ hne
      simp only [Prod.mk.eta] at hpos
      nlinarith))
    (fun _ _ => labO_isOpen hm hmN ρ)
    (fun _ _ Q hQ => labA_mono hm hmN hρ'0.le (hρρ'.trans' (le_mul_of_one_le_left hρ'0.le
      (Real.one_le_exp zero_le_one))) hQ)
    (fun _ _ Q hQ => labA_sub_Tset hm hmN hρs hQ) (fun _ _ Q hQ => Cset_sub_labO hm hmN hρ'0 Q hQ)
    (fun _ _ => Cset_subset hm hmN hR₀) (c₀ := (2 * π * m) ^ 2)
    (fun _ _ y hy => Cset_val hm hmN hR₀ hQ' hy r lam) (η := C₁ * sT)
    (fun _ _ y => βf_bound hm hmN hR₀ hR₀1 hcF hsqF hsT hr hlam hrs hC₁ hMΨ y)
    (aw := a) (bw := b) le_rfl le_rfl hac hcb
    (fun _ _ y hy => Tset_val hm hmN hR₀ hR₀1 hcF hsqF hsT hCQ hQ' hη hη' hy)
    (fun q hq1 hq2 hqc => mem_iUnion₂.mpr ⟨(), Finset.mem_univ _,
      crit_mem_Tset hδ2 ha hlo hhi hsT0.le q hq1 hq2 (hshort q hq2) hqc⟩)
    (fun _ => (2 * m - 1) * (n - 1))
    (fun _ _ _ _ k => finrank (ZMod 2)
      (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k))
    (fun _ _ {V} {KL} hL hV0 {g} {O} hg hsupp hle hVT hgT {a₀a} {b₀a} ha₀a hb₀a hgc hK {R} hR
        hdis hstrict => by
      obtain ⟨d, hd, h⟩ := crossing_lens hm hmN hL hV0 hg hsupp hle hn hsmall hρ'0 hρρ'
        (fun Q hQ => hVT Q (labA_sub_Tset hm hmN hρs hQ))
        (fun Q hQ => (hgT Q (labA_sub_Tset hm hmN hρs hQ)).trans
          (penβ_labA hm hmN hr hlam hρr hQ))
        ha₀a hb₀a hgc hK hR hdis hstrict
      exact ⟨d, hd, fun a c t ht ha hc hca => ⟨(h a c t ht ha hc hca).1,
        (h a c t ht ha hc hca).2.1, fun k => (h a c t ht ha hc hca).2.2 k (hV2 k)⟩⟩)
    hab
  have h := hcross ((2 * π * m) ^ 2 - d / 4) ((2 * π * m) ^ 2 + d / 4) 1 le_rfl (by linarith)
    (by linarith) (by linarith) q
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  exact h

end

end Finsler.RoundLevel
