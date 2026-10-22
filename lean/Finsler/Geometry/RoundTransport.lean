module

public import Finsler.Geometry.RoundModelLens
public import Finsler.Geometry.AmbientDescent
public import Finsler.Topology.LensTransport
public import Finsler.Topology.LensTrap

/-! Transport of the lens pairs between the polygons and the model near the regular m-gons.

The ambient label set of radius ρ is the set of good polygons whose inverse chart has negative
and positive squares below ρ². For ρ small the inverse chart is a homeomorphism of the ambient
label set (as a subset of the polygons with nonzero vertices) onto the label set of the model.

For a Lipschitz field V which is the push-forward W of the model field (0, J z ξ) on the ambient
label set, the flows correspond:

* if the model orbit stays in the label set up to the time T, the chart of the model orbit
  solves the equation of V, so it is the orbit of V (uniqueness for Lipschitz fields);
* if the orbit of V stays in the ambient label set up to the time T, its inverse chart has
  derivative (0, J z ξ): the frame z is constant and the fibre part solves the linear equation
  ξ' = J z ξ, so it is the model orbit.

With the trapping of the descent (outside a smaller label set and an open set disjoint from the
label set the time-one map decreases the function) and the margin of the model flow on a unit
time interval, the orbits of points of the ambient label set stay in it as long as they are not
taken below the lower cut. The lens transport then identifies the lens pair of the ambient label
set with the lens pair of the model label set, whose cohomology is the cohomology of V₂ shifted by
(2m − 1)(n − 1). -/

@[expose] public section

namespace Finsler.RoundTransport

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundCoords Finsler.RoundSpectral Finsler.RoundModes Finsler.AmbientPenalty
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundLabel Finsler.RoundModel Finsler.RoundQR
open Finsler.RoundCone Finsler.RoundThom Finsler.RoundModelLens Finsler.ConeLens Finsler.FlowLens
open Finsler.LensContinuation Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.AmbientDescent Module
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)

/-! ### The label sets and the field -/

/-- The push-forward of the model field. -/
def fieldW (Q : ZMod N → Ambient n) : ZMod N → Ambient n :=
  lin m (unchart hm hmN Q).1 (J hm hmN (unchart hm hmN Q).1 (unchart hm hmN Q).2)

/-- The ambient label set. -/
def labA (ρ : ℝ) : Set (ZMod N → Ambient n) :=
  {Q | Good m Q ∧ sqN (unchart hm hmN Q) < ρ ^ 2 ∧ sqP (unchart hm hmN Q) < ρ ^ 2}

/-- The ambient label set in the polygons with nonzero vertices. -/
def labO (ρ : ℝ) : Set (Om n N) := {Q | Q.1 ∈ labA hm hmN ρ}

variable (n N) in
/-- Radii for which the chart of the model label set has nonzero vertices. -/
def Small (m : ℕ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ ∀ p : (Ambient n × Ambient n) × Fib n N m, p.1 ∈ V2 → sqN p < ρ ^ 2 →
    sqP p < ρ ^ 2 → ∀ j, chart m p j ≠ 0


theorem tri_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {p : (Ambient n × Ambient n) × Fib n N m}
    (hP : sqP p < ρ ^ 2) : 0 < 1 + p.2.1.1 ∧ 0 < 1 + p.2.1.2.2 := by
  have h0 := pair_self_nonneg ((p.2.2 : ZMod N → Ambient n) - negP p)
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
  unfold sqP at hP
  have h1 : p.2.1.1 ^ 2 < 1 := by nlinarith [sq_nonneg p.2.1.2.1, sq_nonneg p.2.1.2.2]
  have h3 : p.2.1.2.2 ^ 2 < 1 := by nlinarith [sq_nonneg p.2.1.2.1, sq_nonneg p.2.1.1]
  constructor <;> nlinarith

theorem chart_mem {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {p : (Ambient n × Ambient n) × Fib n N m}
    (hp : p.1 ∈ V2) (hN : sqN p < ρ ^ 2) (hP : sqP p < ρ ^ 2) :
    chart m p ∈ labA hm hmN ρ ∧ unchart hm hmN (chart m p) = p := by
  obtain ⟨h1, h3⟩ := tri_pos hρ0 hρ1 hP
  obtain ⟨hg, he⟩ := unchart_chart hm hmN (z := p.1) (ξ := p.2) hp h1 h3
  simp only [Prod.mk.eta] at hg he
  exact ⟨⟨hg, by rw [he]; exact hN, by rw [he]; exact hP⟩, he⟩

theorem unchart_continuousOn : ContinuousOn (unchart (n := n) (N := N) hm hmN) {Q | Good m Q} :=
  fun _ hQ => (unchart_contDiffAt hm hmN hQ).continuousAt.continuousWithinAt

theorem labA_isOpen (ρ : ℝ) : IsOpen (labA (n := n) (N := N) hm hmN ρ) :=
  (unchart_continuousOn hm hmN).isOpen_inter_preimage (good_m_isOpen (m := m))
    ((isOpen_lt (sqN_contDiff (n := n) (N := N) (m := m)).continuous continuous_const).inter
      (isOpen_lt (sqP_contDiff (n := n) (N := N) (m := m)).continuous continuous_const))

theorem labO_isOpen (ρ : ℝ) : IsOpen (labO (n := n) (N := N) hm hmN ρ) :=
  (labA_isOpen hm hmN ρ).preimage continuous_subtype_val

theorem labA_mono {ρ ρ' : ℝ} (hρ' : 0 ≤ ρ') (h : ρ' ≤ ρ) :
    labA (n := n) (N := N) hm hmN ρ' ⊆ labA hm hmN ρ := by
  intro Q hQ
  have h2 : ρ' ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hρ' h 2
  exact ⟨hQ.1, hQ.2.1.trans_le h2, hQ.2.2.trans_le h2⟩

/-! ### The homeomorphism of the label sets -/

/-- The inverse chart on the ambient label set. -/
def toLab {ρ : ℝ} (Q : labO (n := n) (N := N) hm hmN ρ) : labelM (n := n) (N := N) (m := m) ρ :=
  ⟨⟨unchart hm hmN Q.1.1, unchart_mem_V2 hm hmN Q.2.1⟩, Q.2.2.1, Q.2.2.2⟩

/-- The chart on the model label set. -/
def ofLab {ρ : ℝ} (hρ : Small n N m ρ) (w : labelM (n := n) (N := N) (m := m) ρ) :
    labO (n := n) (N := N) hm hmN ρ :=
  ⟨⟨chart m w.1.1, hρ.2.2 w.1.1 w.1.2 w.2.1 w.2.2⟩,
    (chart_mem hm hmN hρ.1 hρ.2.1 w.1.2 w.2.1 w.2.2).1⟩

/-- **The label sets are homeomorphic.** -/
def homeo {ρ : ℝ} (hρ : Small n N m ρ) :
    labO (n := n) (N := N) hm hmN ρ ≃ₜ labelM (n := n) (N := N) (m := m) ρ where
  toFun := toLab hm hmN
  invFun := ofLab hm hmN hρ
  left_inv Q := Subtype.ext (Subtype.ext (chart_unchart hm hmN Q.2.1))
  right_inv w := Subtype.ext (Subtype.ext (chart_mem hm hmN hρ.1 hρ.2.1 w.1.2 w.2.1 w.2.2).2)
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have h : ContinuousOn (unchart (n := n) (N := N) hm hmN) (labA hm hmN ρ) :=
      (unchart_continuousOn hm hmN).mono fun _ hQ => hQ.1
    exact h.comp_continuous (continuous_subtype_val.comp continuous_subtype_val) fun Q => Q.2
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (chart_contDiff (n := n) (N := N) m).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)

theorem homeo_apply {ρ : ℝ} (hρ : Small n N m ρ) (Q : labO (n := n) (N := N) hm hmN ρ) :
    ((homeo hm hmN hρ Q : MS n N m) : (Ambient n × Ambient n) × Fib n N m) =
      unchart hm hmN Q.1.1 := rfl

/-! ### Derivatives in the chart -/


theorem chart_line (z : Ambient n × Ambient n) (ξ v : Fib n N m) (t : ℝ) :
    chart m (z, ξ + t • v) = chart m (z, ξ) + t • lin m z v := by
  simp only [chart, map_add, map_smul]
  abel

/-- The derivative of the inverse chart along the fibre directions. -/
theorem fderiv_unchart_lin {p : (Ambient n × Ambient n) × Fib n N m} (hp : p.1 ∈ V2)
    (h1 : 0 < 1 + p.2.1.1) (h3 : 0 < 1 + p.2.1.2.2) (v : Fib n N m) :
    fderiv ℝ (unchart hm hmN) (chart m p) (lin m p.1 v) = (0, v) := by
  obtain ⟨z, ξ⟩ := p
  have hgood := (unchart_chart hm hmN hp h1 h3).1
  have hd : DifferentiableAt ℝ (unchart (n := n) (N := N) hm hmN) (chart m (z, ξ)) :=
    (unchart_contDiffAt hm hmN hgood).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => chart m (z, ξ + t • v)) (lin m z v) 0 := by
    have e : (fun t : ℝ => chart m (z, ξ + t • v)) = fun t => chart m (z, ξ) + t • lin m z v := by
      funext t
      exact chart_line z ξ v t
    rw [e]
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (lin m z v)).const_add (chart m (z, ξ))
    rwa [one_smul] at h
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hev : (fun t : ℝ => ((z, ξ + t • v) : (Ambient n × Ambient n) × Fib n N m)) =ᶠ[𝓝 0]
      (unchart hm hmN ∘ fun t : ℝ => chart m (z, ξ + t • v)) := by
    have hc1 : ContinuousAt (fun t : ℝ => 1 + (ξ + t • v).1.1) 0 := by fun_prop
    have hc3 : ContinuousAt (fun t : ℝ => 1 + (ξ + t • v).1.2.2) 0 := by fun_prop
    have e1 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + (ξ + t • v).1.1 :=
      hc1.eventually (lt_mem_nhds (by simpa using h1))
    have e3 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + (ξ + t • v).1.2.2 :=
      hc3.eventually (lt_mem_nhds (by simpa using h3))
    filter_upwards [e1, e3] with t ht1 ht3
    exact (unchart_chart hm hmN hp ht1 ht3).2.symm
  have h2 : HasDerivAt (fun t : ℝ => ((z, ξ + t • v) : (Ambient n × Ambient n) × Fib n N m))
      ((0 : Ambient n × Ambient n), v) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξ
    rw [one_smul] at h
    exact (hasDerivAt_const (0 : ℝ) z).prodMk h
  exact (hc.congr_of_eventuallyEq hev).unique h2


/-- The reflection is the negative part minus the positive part. -/
theorem J_eq (z : Ambient n × Ambient n) (ζ : Fib n N m) :
    J hm hmN z ζ = negF hm hmN (z, ζ) - posF hm hmN (z, ζ) := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [(J_apply hm hmN z ζ).1]
    simp [posF, negF]
  · rw [(J_apply hm hmN z ζ).2]
    simp only [posF, Prod.snd_sub, Submodule.coe_sub, coe_negF, negP]
    rw [two_smul]
    abel

/-- The fibre part of the model flow. -/
theorem hasDerivAt_fibM (w : MS n N m) (s : ℝ) :
    HasDerivAt (fun s => ((descentM hm hmN).flow s w).1.2)
      (Real.exp s • negF hm hmN w.1 - Real.exp (-s) • posF hm hmN w.1) s := by
  change HasDerivAt (fun s => Real.exp s • negF hm hmN w.1 + Real.exp (-s) • posF hm hmN w.1) _ s
  have h1 := (Real.hasDerivAt_exp s).smul_const (negF hm hmN w.1)
  have h2 := ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).smul_const (posF hm hmN w.1)
  convert h1.fun_add h2 using 1
  · funext i
    rfl
  · rw [mul_neg_one, neg_smul, sub_eq_add_neg]

/-- The model field along the model flow. -/
theorem J_fibM (w : MS n N m) (s : ℝ) :
    J hm hmN w.1.1 ((descentM hm hmN).flow s w).1.2 =
      Real.exp s • negF hm hmN w.1 - Real.exp (-s) • posF hm hmN w.1 := by
  change J hm hmN w.1.1 (Real.exp s • negF hm hmN w.1 + Real.exp (-s) • posF hm hmN w.1) = _
  rw [J_eq, negF_scale hm hmN w.2, posF_scale hm hmN w.2]

/-! ### Comparison of the flows -/

section Compare

variable {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {KL : ℝ≥0} (hL : LipschitzWith KL V)
  {ρ : ℝ} (hρ : Small n N m ρ) (hVW : ∀ Q ∈ labA hm hmN ρ, V Q = fieldW hm hmN Q)

include hρ hVW in
/-- **The chart of a model orbit staying in the label set is an orbit of the field.** -/
theorem flow_eq_chart (w : MS n N m) {T : ℝ}
    (hstay : ∀ s ∈ Icc (0 : ℝ) T, (descentM hm hmN).flow s w ∈ labelM ρ) :
    ∀ s ∈ Icc (0 : ℝ) T,
      ODE.globalSolution V hL (chart m w.1) s = chart m ((descentM hm hmN).flow s w).1 := by
  have hcurve : ∀ s, HasDerivAt (fun s => chart m ((descentM hm hmN).flow s w).1)
      (lin m w.1.1 (Real.exp s • negF hm hmN w.1 - Real.exp (-s) • posF hm hmN w.1)) s := by
    intro s
    have h := (lin m w.1.1).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_fibM hm hmN w s)
    exact h.const_add (regular N m w.1.1.1 w.1.1.2)
  have hfield : ∀ s ∈ Icc (0 : ℝ) T,
      lin m w.1.1 (Real.exp s • negF hm hmN w.1 - Real.exp (-s) • posF hm hmN w.1) =
        V (chart m ((descentM hm hmN).flow s w).1) := by
    intro s hs
    obtain ⟨hmem, hun⟩ := chart_mem hm hmN hρ.1 hρ.2.1 ((descentM hm hmN).flow s w).2
      (hstay s hs).1 (hstay s hs).2
    rw [hVW _ hmem, fieldW, hun, ← J_fibM hm hmN w s]
    rfl
  intro s hs
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => V) (s := fun _ => univ) (K := KL)
    (fun _ _ => hL.lipschitzOnWith) (ODE.continuous_globalSolution_apply V hL _).continuousOn
    (fun t _ => (ODE.hasDerivAt_globalSolution V hL _ t).hasDerivWithinAt) (fun _ _ => trivial)
    (continuous_iff_continuousAt.mpr fun t => (hcurve t).continuousAt).continuousOn
    (fun t ht => by
      rw [← hfield t (Ico_subset_Icc_self ht)]
      exact (hcurve t).hasDerivWithinAt) (fun _ _ => trivial) ?_ hs
  rw [ODE.globalSolution_zero, (descentM hm hmN).zero]

include hρ hVW in
/-- **The inverse chart of an orbit of the field staying in the label set is a model orbit.** -/
theorem unchart_flow_eq (Q : ZMod N → Ambient n) (hQ : Q ∈ labA hm hmN ρ) {T : ℝ}
    (hstay : ∀ s ∈ Icc (0 : ℝ) T, ODE.globalSolution V hL Q s ∈ labA hm hmN ρ) :
    ∀ s ∈ Icc (0 : ℝ) T, unchart hm hmN (ODE.globalSolution V hL Q s) =
      ((descentM hm hmN).flow s ⟨unchart hm hmN Q, unchart_mem_V2 hm hmN hQ.1⟩).1 := by
  -- the derivative of the inverse chart along the orbit
  have hδ : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => unchart hm hmN (ODE.globalSolution V hL Q s))
      ((0 : Ambient n × Ambient n),
        J hm hmN (unchart hm hmN (ODE.globalSolution V hL Q s)).1
          (unchart hm hmN (ODE.globalSolution V hL Q s)).2) s := by
    intro s hs
    obtain ⟨hg, hN, hP⟩ := hstay s hs
    have hd : DifferentiableAt ℝ (unchart (n := n) (N := N) hm hmN) (ODE.globalSolution V hL Q s) :=
      (unchart_contDiffAt hm hmN hg).differentiableAt (by simp)
    have h := hd.hasFDerivAt.comp_hasDerivAt s (ODE.hasDerivAt_globalSolution V hL Q s)
    obtain ⟨h1, h3⟩ := tri_pos hρ.1 hρ.2.1 hP
    have hc := chart_unchart hm hmN hg
    have hv := fderiv_unchart_lin hm hmN (unchart_mem_V2 hm hmN hg) h1 h3
      (J hm hmN (unchart hm hmN (ODE.globalSolution V hL Q s)).1
        (unchart hm hmN (ODE.globalSolution V hL Q s)).2)
    rw [hc] at hv
    rw [hVW _ (hstay s hs), fieldW, hv] at h
    exact h
  -- the frame is constant
  have hz : ∀ s ∈ Icc (0 : ℝ) T, (unchart hm hmN (ODE.globalSolution V hL Q s)).1 =
      (unchart hm hmN Q).1 := by
    have h := constant_of_has_deriv_right_zero
      (f := fun s => (unchart hm hmN (ODE.globalSolution V hL Q s)).1) (a := 0) (b := T)
      (fun s hs => ((hasFDerivAt_fst.comp_hasDerivAt s (hδ s hs)).continuousAt).continuousWithinAt)
      (fun s hs => by
        have h := hasFDerivAt_fst.comp_hasDerivAt s (hδ s (Ico_subset_Icc_self hs))
        simpa [Function.comp_def] using h.hasDerivWithinAt)
    intro s hs
    have h0 := h s hs
    simp only [ODE.globalSolution_zero] at h0
    exact h0
  -- the fibre part solves the linear equation of the frame
  set w₀ : MS n N m := ⟨unchart hm hmN Q, unchart_mem_V2 hm hmN hQ.1⟩ with hw₀
  have hsnd : ∀ s ∈ Icc (0 : ℝ) T, (unchart hm hmN (ODE.globalSolution V hL Q s)).2 =
      ((descentM hm hmN).flow s w₀).1.2 := by
    intro s hs
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => (J hm hmN (unchart hm hmN Q).1 : Fib n N m → Fib n N m))
      (s := fun _ => univ) (K := ‖J hm hmN (unchart hm hmN Q).1‖₊)
      (fun _ _ => (J hm hmN (unchart hm hmN Q).1).lipschitz.lipschitzOnWith)
      (fun s hs => ((hasFDerivAt_snd.comp_hasDerivAt s (hδ s hs)).continuousAt).continuousWithinAt)
      (fun s hs => ?_) (fun _ _ => trivial)
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_fibM hm hmN w₀ t).continuousAt).continuousOn
      (fun t _ => ?_) (fun _ _ => trivial) ?_ hs
    · have h := hasFDerivAt_snd.comp_hasDerivAt s (hδ s (Ico_subset_Icc_self hs))
      rw [← hz s (Ico_subset_Icc_self hs)]
      simpa [Function.comp_def] using h.hasDerivWithinAt
    · have h := (hasDerivAt_fibM hm hmN w₀ t).hasDerivWithinAt (s := Ici t)
      rw [← J_fibM hm hmN w₀ t] at h
      exact h
    · show (unchart hm hmN (ODE.globalSolution V hL Q 0)).2 = ((descentM hm hmN).flow 0 w₀).1.2
      rw [ODE.globalSolution_zero, (descentM hm hmN).zero]
  intro s hs
  refine Prod.ext ?_ (hsnd s hs)
  rw [hz s hs]
  rfl

/-- The model flow keeps a margin: in a unit time it takes the label set of radius ρ' into the
label set of radius e ρ'. -/
theorem flowM_mem_margin {ρ' : ℝ} (hρ'0 : 0 ≤ ρ') (hρρ' : Real.exp 1 * ρ' ≤ ρ) (w : MS n N m)
    (hw : w ∈ labelM (n := n) (N := N) (m := m) ρ') {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (descentM hm hmN).flow s w ∈ labelM ρ := by
  have he : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.mpr hs1
  have he0 := Real.exp_pos s
  have h1 : Real.exp s ^ 2 * ρ' ^ 2 ≤ ρ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) ((mul_le_mul_of_nonneg_right he hρ'0).trans hρρ') 2
  have hρ' : ρ' ≤ ρ := (le_mul_of_one_le_left hρ'0 (Real.one_le_exp zero_le_one)).trans hρρ'
  have h2 : ρ' ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hρ'0 hρ' 2
  have hes : Real.exp (-s) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
  refine ⟨?_, ?_⟩
  · rw [flowM_sqN]
    have := hw.1
    have hN := sqN_nonneg w.1
    have : Real.exp s ^ 2 * sqN w.1 < Real.exp s ^ 2 * ρ' ^ 2 :=
      mul_lt_mul_of_pos_left hw.1 (by positivity)
    linarith
  · rw [flowM_sqP]
    have hP := sqP_nonneg w.1
    have : Real.exp (-s) ^ 2 * sqP w.1 ≤ sqP w.1 := by nlinarith
    linarith [hw.2]

include hρ hVW in
/-- **The margin.** Orbits of points of the label set of radius ρ' stay in the label set of radius
ρ for a unit time. -/
theorem margin {ρ' : ℝ} (hρ'0 : 0 < ρ') (hρρ' : Real.exp 1 * ρ' ≤ ρ) (Q : ZMod N → Ambient n)
    (hQ : Q ∈ labA hm hmN ρ') {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ODE.globalSolution V hL Q s ∈ labA hm hmN ρ := by
  set w₀ : MS n N m := ⟨unchart hm hmN Q, unchart_mem_V2 hm hmN hQ.1⟩ with hw₀
  have hw : w₀ ∈ labelM (n := n) (N := N) (m := m) ρ' := ⟨hQ.2.1, hQ.2.2⟩
  have hstay : ∀ r ∈ Icc (0 : ℝ) 1, (descentM hm hmN).flow r w₀ ∈ labelM ρ :=
    fun r hr => flowM_mem_margin hm hmN hρ'0.le hρρ' w₀ hw hr.1 hr.2
  have h := flow_eq_chart hm hmN hL hρ hVW w₀ hstay s ⟨hs0, hs1⟩
  have hc : chart m w₀.1 = Q := chart_unchart hm hmN hQ.1
  rw [hc] at h
  rw [h]
  exact (chart_mem hm hmN hρ.1 hρ.2.1 ((descentM hm hmN).flow s w₀).2 (hstay s ⟨hs0, hs1⟩).1
    (hstay s ⟨hs0, hs1⟩).2).1

end Compare

/-! ### The lens pair of the ambient label set -/

section Crossing

variable {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {KL : ℝ≥0} (hL : LipschitzWith KL V)
  (hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod N → Ambient n) → ℝ} {O : Set (ZMod N → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)


theorem descentOf_flow_val {s : ℝ} (hs : 0 ≤ s) (Q : Om n N) :
    ((descentOf hL hV0 hg hsupp hle).flow s Q).1 = ODE.globalSolution V hL Q.1 s := by
  change ODE.globalSolution V hL Q.1 (max s 0) = _
  rw [max_eq_left hs]

/-- **The lens pair of the ambient label set at the m-gons.** -/
theorem crossing_lens (hn : 1 ≤ n) {ρ ρ' : ℝ} (hρ : Small n N m ρ) (hρ'0 : 0 < ρ')
    (hρρ' : Real.exp 1 * ρ' ≤ ρ)
    (hVW : ∀ Q ∈ labA hm hmN ρ, V Q = fieldW hm hmN Q)
    (hgM : ∀ Q ∈ labA hm hmN ρ, g Q = model m (unchart hm hmN Q))
    {a₀a b₀a : ℝ} (ha₀ : a₀a < (2 * π * m) ^ 2) (hb₀ : (2 * π * m) ^ 2 < b₀a)
    (hgc : Continuous (fun Q : Om n N => g Q.1))
    (hK : IsCompact {Q : Om n N | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a})
    {R : Set (Om n N)} (hR : IsOpen R) (hdis : Disjoint (labO hm hmN ρ) R)
    (hstrict : ∀ Q : Om n N, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ labO hm hmN ρ' ∪ R →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < (2 * π * m) ^ 2 → (2 * π * m) ^ 2 < c →
      c - a < d →
      (∀ k : ℕ, finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
          (fun Q : Om n N => g Q.1) (descentOf hL hV0 hg hsupp hle) (labO hm hmN ρ) a c t)))
            (k + (2 * m - 1) * (n - 1))) =
        finrank (ZMod 2)
          (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k)) ∧
      (∀ k : ℕ, k < (2 * m - 1) * (n - 1) → ∀ x : H (triv (pairOf (partY_sub_partU
          (fun Q : Om n N => g Q.1) (descentOf hL hV0 hg hsupp hle) (labO hm hmN ρ) a c t))) k,
        x = 0) ∧
      (∀ k : ℕ, Module.Finite (ZMod 2)
          (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k) →
        Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU
          (fun Q : Om n N => g Q.1) (descentOf hL hV0 hg hsupp hle) (labO hm hmN ρ) a c t)))
            (k + (2 * m - 1) * (n - 1)))) := by
  set D₁ := descentOf hL hV0 hg hsupp hle with hD₁
  have hρ0 : 0 < ρ := hρ.1
  have hρ' : ρ' ≤ ρ := (le_mul_of_one_le_left hρ'0.le (Real.one_le_exp zero_le_one)).trans hρρ'
  have hsub : labO (n := n) (N := N) hm hmN ρ' ⊆ labO hm hmN ρ :=
    fun Q hQ => labA_mono hm hmN hρ'0.le hρ' hQ
  obtain ⟨d₁, hd₁, htrap⟩ := Finsler.LensTrap.exists_trap D₁ hgc
    ((labO_isOpen hm hmN ρ').union hR) hK hstrict
  refine ⟨min d₁ (min ((2 * π * m) ^ 2 - a₀a) (min (b₀a - (2 * π * m) ^ 2) (ρ ^ 2 / 8))),
    lt_min hd₁ (lt_min (by linarith) (lt_min (by linarith) (by positivity))),
    fun a c t ht ha hc hd => ?_⟩
  have hd1 : c - a < d₁ := hd.trans_le (min_le_left _ _)
  have hd2 : c - a < (2 * π * m) ^ 2 - a₀a :=
    hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : c - a < b₀a - (2 * π * m) ^ 2 :=
    hd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd4 : c - a < ρ ^ 2 / 8 :=
    hd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have haa : a₀a ≤ a := by linarith
  have hcb : c ≤ b₀a := by linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  -- the trapping in unit time
  have htrap1 : ∀ w : Om n N, g w.1 < c → a ≤ g (D₁.flow 1 w).1 → w ∈ labO hm hmN ρ' ∪ R :=
    htrap a c 1 haa hcb hd1 le_rfl
  -- the trapping of the polygons
  have hS₁ : ∀ w, w ∈ labO hm hmN ρ → g w.1 < c → a ≤ g (D₁.flow t w).1 → ∀ s, 0 ≤ s → s ≤ t →
      D₁.flow s w ∈ labO hm hmN ρ := by
    intro w hw hwc hwa s hs hst
    set s₁ := max (s - 1) 0 with hs₁
    have hs₁0 : 0 ≤ s₁ := le_max_right _ _
    have hs₁s : s₁ ≤ s := max_le (by linarith) hs
    have hs₁t : 1 + s₁ ≤ t := by
      rcases le_total (s - 1) 0 with h | h
      · rw [hs₁, max_eq_right h]
        linarith
      · rw [hs₁, max_eq_left h]
        linarith
    have hs₂1 : s - s₁ ≤ 1 := by
      have : s - 1 ≤ s₁ := le_max_left _ _
      linarith
    have ha' : a ≤ g (D₁.flow 1 (D₁.flow s₁ w)).1 := by
      rw [← D₁.add 1 s₁ w zero_le_one hs₁0]
      exact hwa.trans (Finsler.LensTrap.mono_time D₁ (by linarith) hs₁t w)
    have hin : D₁.flow s₁ w ∈ labO hm hmN ρ :=
      Finsler.LensTrap.trap_piece D₁ zero_le_one (labO_isOpen hm hmN ρ) hR hdis
        (fun w' h1 h2 => (htrap1 w' h1 h2).elim (fun h => Or.inl (hsub h)) Or.inr)
        w hw hwc s₁ hs₁0 ha'
    have hin' : D₁.flow s₁ w ∈ labO hm hmN ρ' := by
      rcases htrap1 _ (lt_of_le_of_lt (D₁.mono s₁ w hs₁0) hwc) ha' with h | h
      · exact h
      · exact absurd h (Set.disjoint_left.mp hdis hin)
    have hsplit : D₁.flow s w = D₁.flow (s - s₁) (D₁.flow s₁ w) := by
      rw [← D₁.add (s - s₁) s₁ w (by linarith) hs₁0, sub_add_cancel]
    rw [hsplit]
    change (D₁.flow (s - s₁) (D₁.flow s₁ w)).1 ∈ labA hm hmN ρ
    rw [descentOf_flow_val hL hV0 hg hsupp hle (by linarith)]
    exact margin hm hmN hL hρ hVW hρ'0 hρρ' _ hin' (by linarith) hs₂1
  -- the trapping of the model
  have hρc : 4 * (c - a) < ρ ^ 2 := by linarith
  have hS₂ : ∀ w, w ∈ labelM (n := n) (N := N) (m := m) ρ → (cone hm hmN).energy w < c →
      a ≤ (cone hm hmN).energy ((descentM hm hmN).flow t w) → ∀ s, 0 ≤ s → s ≤ t →
      (descentM hm hmN).flow s w ∈ labelM ρ :=
    fun w hw hwc hwa s hs hst => model_trap hm hmN hc.le ha.le ht hρc w hw hwc hwa s hs hst
  -- the values correspond
  have hgv : ∀ w : labO (n := n) (N := N) hm hmN ρ,
      (cone hm hmN).energy (homeo hm hmN hρ w : MS n N m) = g (w : Om n N).1 := by
    intro w
    rw [cone_energy, homeo_apply]
    exact (hgM _ w.2).symm
  have hA₁ : ∀ w : labO (n := n) (N := N) hm hmN ρ,
      (∀ s, 0 ≤ s → s ≤ t → D₁.flow s (w : Om n N) ∈ labO hm hmN ρ) →
      (cone hm hmN).energy ((descentM hm hmN).flow t (homeo hm hmN hρ w : MS n N m)) =
        g (D₁.flow t (w : Om n N)).1 := by
    intro w hstay
    have hst : ∀ s ∈ Icc (0 : ℝ) t, ODE.globalSolution V hL w.1.1 s ∈ labA hm hmN ρ := by
      intro s hs
      have h := hstay s hs.1 hs.2
      change (D₁.flow s w).1 ∈ labA hm hmN ρ at h
      rwa [descentOf_flow_val hL hV0 hg hsupp hle hs.1] at h
    have h := unchart_flow_eq hm hmN hL hρ hVW w.1.1 w.2 hst t ⟨ht0, le_rfl⟩
    rw [cone_energy, descentOf_flow_val hL hV0 hg hsupp hle ht0,
      hgM _ (hst t ⟨ht0, le_rfl⟩), h]
    rfl
  have hA₂ : ∀ w : labO (n := n) (N := N) hm hmN ρ,
      (∀ s, 0 ≤ s → s ≤ t → (descentM hm hmN).flow s (homeo hm hmN hρ w : MS n N m) ∈ labelM ρ) →
      (cone hm hmN).energy ((descentM hm hmN).flow t (homeo hm hmN hρ w : MS n N m)) =
        g (D₁.flow t (w : Om n N)).1 := by
    intro w hstay
    have h := flow_eq_chart hm hmN hL hρ hVW (homeo hm hmN hρ w : MS n N m) (T := t)
      (fun s hs => hstay s hs.1 hs.2) t ⟨ht0, le_rfl⟩
    have hc0 : chart m (homeo hm hmN hρ w : MS n N m).1 = w.1.1 := by
      rw [homeo_apply]
      exact chart_unchart hm hmN w.2.1
    rw [hc0] at h
    obtain ⟨hmem, hun⟩ := chart_mem hm hmN hρ.1 hρ.2.1
      ((descentM hm hmN).flow t (homeo hm hmN hρ w : MS n N m)).2 (hstay t ht0 le_rfl).1
      (hstay t ht0 le_rfl).2
    rw [cone_energy, descentOf_flow_val hL hV0 hg hsupp hle ht0, h, hgM _ hmem, hun]
  -- the transport
  have hbij := fun q : ℕ => Finsler.LensTransport.part_bijective D₁ (descentM hm hmN)
    (homeo hm hmN hρ) hgv hS₁ hS₂ hA₁ hA₂ q
  -- the label set of the model and the whole model
  have hcore : ∀ q : ℕ, Nonempty (H (triv (pairOf (partY_sub_partU (cone hm hmN).energy
      (descentM hm hmN) (labelM (n := n) (N := N) (m := m) ρ) a c t))) q ≃ₗ[ZMod 2]
        H (triv (pairOf (partY_sub_partU (cone hm hmN).energy (descentM hm hmN)
          (univ : Set (MS n N m)) a c t))) q) := fun q =>
    nonempty_label_equiv hm hmN (a' := a - ρ ^ 2 / 16) (by linarith [sq_pos_of_pos hρ0])
      hc.le (by linarith [sq_pos_of_pos hρ0]) ht (by linarith) q
  refine ⟨fun k => ?_, fun k hk x => ?_, fun k hk => ?_⟩
  · obtain ⟨e₂⟩ := hcore (k + (2 * m - 1) * (n - 1))
    rw [← (LinearEquiv.ofBijective _ (hbij _)).finrank_eq, e₂.finrank_eq]
    exact model_lens_finrank hm hmN ha.le hc ht0 hn k
  · obtain ⟨e₂⟩ := hcore k
    let e₁ := LinearEquiv.ofBijective _ (hbij k)
    have h0 : e₂ (e₁.symm x) = 0 := model_lens_zero hm hmN ha.le hc ht0 hn k hk _
    have h1 := (LinearEquiv.map_eq_zero_iff e₂).mp h0
    exact (LinearEquiv.map_eq_zero_iff e₁.symm).mp h1
  · obtain ⟨e₂⟩ := hcore (k + (2 * m - 1) * (n - 1))
    haveI : Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU (cone hm hmN).energy
        (descentM hm hmN) (univ : Set (MS n N m)) a c t))) (k + (2 * m - 1) * (n - 1))) :=
      model_lens_finite hm hmN ha.le hc ht0 hn k hk
    haveI := Module.Finite.equiv e₂.symm
    exact Module.Finite.equiv (LinearEquiv.ofBijective _ (hbij _))

end Crossing

end

end Finsler.RoundTransport
