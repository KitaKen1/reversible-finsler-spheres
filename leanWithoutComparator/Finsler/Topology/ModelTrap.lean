module

public import Finsler.Topology.ProductModel

/-! Bounded label sets of the product model. For the product model h(z) - |u|² + |y|² with the
product flow (ψ_t z, e^t u, e^{-t} y), a point below b which the flow does not take below a in
time T ≥ 1 has small fibre coordinates: (e^{2T} - 1)|u|² + (1 - e^{-2T})|y|² < b - a, so
|u|² < b - a and |y|² < 2(b - a), and e^{2T}|u|² < 2(b - a). Hence, if b - a < ρ²/2, a set S of
the model which contains all points over a base set WB with fibres of norm below ρ and lies over
WB has the same points not taken below a (or below any a' < b with b - a' < ρ²/2) as the set of
all points over WB; and if whole orbits of the base points stay in WB up to the time T (with the
widened cuts of the base estimates), whole orbits of the points of S stay in S. -/

@[expose] public section

namespace Finsler.ModelTrap

open CategoryTheory Set Topology Finsler.FlowLens Finsler.ConeLens Finsler.ProductModel

noncomputable section

variable {B : TopCat.{0}} {h : B → ℝ} (k : ℕ) (V : Type) [NormedAddCommGroup V]
  [NormedSpace ℝ V] (ψ : Descent B h)

/-- **The fibre estimate.** -/
theorem fibre_estimate (hh : Continuous h) {a b T : ℝ} {w : Model B k V}
    (hw : (cone k V hh).energy w < b)
    (hw' : a ≤ (cone k V hh).energy ((descent k V ψ hh).flow T w)) (hT : 0 ≤ T) :
    (Real.exp (2 * T) - 1) * ‖w.2.1‖ ^ 2 + (1 - 1 / Real.exp (2 * T)) * ‖w.2.2‖ ^ 2 < b - a := by
  rw [cone_energy] at hw
  rw [energy_flow] at hw'
  have hmono := ψ.mono T w.1 hT
  have he : 0 < Real.exp (2 * T) := Real.exp_pos _
  have e : ‖w.2.2‖ ^ 2 / Real.exp (2 * T) = 1 / Real.exp (2 * T) * ‖w.2.2‖ ^ 2 := by
    field_simp
  rw [e] at hw'
  nlinarith

/-- With T ≥ 1 the fibre coordinates are small. -/
theorem fibre_small (hh : Continuous h) {a b T : ℝ} {w : Model B k V}
    (hw : (cone k V hh).energy w < b)
    (hw' : a ≤ (cone k V hh).energy ((descent k V ψ hh).flow T w)) (hT : 1 ≤ T) :
    ‖w.2.1‖ ^ 2 < b - a ∧ ‖w.2.2‖ ^ 2 < 2 * (b - a) ∧
      Real.exp (2 * T) * ‖w.2.1‖ ^ 2 < 2 * (b - a) := by
  have h := fibre_estimate k V ψ hh hw hw' (zero_le_one.trans hT)
  have hE : 2 ≤ Real.exp (2 * T) - 1 := by
    have h1 : 2 * T ≥ 2 := by linarith
    have h2 : Real.exp 2 ≥ 3 := by
      have := Real.add_one_le_exp 2
      have h3 : Real.exp 1 ≥ 2 := by
        have := Real.add_one_le_exp 1
        linarith
      have h4 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith
    have h5 := Real.exp_le_exp.mpr h1
    linarith
  have hE' : 1 / 2 ≤ 1 - 1 / Real.exp (2 * T) := by
    have h6 : 1 / Real.exp (2 * T) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (Real.exp_pos _) two_pos]
      linarith
    linarith
  have hu := sq_nonneg ‖w.2.1‖
  have hy := sq_nonneg ‖w.2.2‖
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h7 : Real.exp (2 * T) * ‖w.2.1‖ ^ 2 ≤ 2 * ((Real.exp (2 * T) - 1) * ‖w.2.1‖ ^ 2) := by
    nlinarith
  nlinarith

variable {WB : Set B} {S : Set (Model B k V)} {ρ : ℝ}

/-- **Bounded label sets have the same core as all fibres over the base set.** -/
theorem core_iff (hh : Continuous h) (hS : ∀ w : Model B k V, w.1 ∈ WB → ‖w.2.1‖ < ρ →
      ‖w.2.2‖ < ρ → w ∈ S) (hS' : ∀ w ∈ S, w.1 ∈ WB) (hρpos : 0 < ρ) {a' b T : ℝ} (hT : 1 ≤ T)
    (hab : 2 * (b - a') < ρ ^ 2) (w : Model B k V) (hw : (cone k V hh).energy w < b)
    (hw' : a' < (cone k V hh).energy ((descent k V ψ hh).flow T w)) :
    w ∈ S ↔ w ∈ over k V WB := by
  constructor
  · exact fun h => hS' w h
  · intro hwB
    obtain ⟨hu, hy, -⟩ := fibre_small k V ψ hh hw hw'.le hT
    have hρ : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    have hu' : ‖w.2.1‖ < |ρ| := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
    have hy' : ‖w.2.2‖ < |ρ| := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
    rw [abs_of_pos hρpos] at hu' hy'
    exact hS w hwB hu' hy'

/-- **Whole orbits stay in a bounded label set** if whole orbits of the base points stay in the
base set, with the widened cuts. -/
theorem orbit_stay (hh : Continuous h) (hS : ∀ w : Model B k V, w.1 ∈ WB → ‖w.2.1‖ < ρ →
      ‖w.2.2‖ < ρ → w ∈ S) (hS' : ∀ w ∈ S, w.1 ∈ WB ∧ ‖w.2.2‖ < ρ) {a b T : ℝ} (hT : 1 ≤ T)
    (hab : 2 * (b - a) < ρ ^ 2)
    (hbase : ∀ z, z ∈ WB → h z < b + (b - a) / (Real.exp (2 * T) - 1) →
      a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T z) → ∀ s, 0 ≤ s → s ≤ T →
        ψ.flow s z ∈ WB)
    (w : Model B k V) (hwS : w ∈ S) (hw : (cone k V hh).energy w < b)
    (hw' : a ≤ (cone k V hh).energy ((descent k V ψ hh).flow T w)) (s : ℝ) (hs : 0 ≤ s)
    (hsT : s ≤ T) : (descent k V ψ hh).flow s w ∈ S := by
  obtain ⟨hb1, hb2⟩ := base_estimates (ψ := ψ) hh (by linarith) hw hw'
  obtain ⟨-, -, hu⟩ := fibre_small k V ψ hh hw hw' hT
  obtain ⟨hwB, hy⟩ := hS' w hwS
  rw [descent_flow]
  refine hS _ (hbase w.1 hwB hb1 hb2 s hs hsT) ?_ ?_
  · -- the unstable coordinate grows to at most e^T |u|
    change ‖Real.exp s • w.2.1‖ < ρ
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos s).le]
    have h1 : Real.exp s * ‖w.2.1‖ ≤ Real.exp T * ‖w.2.1‖ :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsT) (norm_nonneg _)
    have h2 : (Real.exp T * ‖w.2.1‖) ^ 2 < ρ ^ 2 := by
      have e : (Real.exp T * ‖w.2.1‖) ^ 2 = Real.exp (2 * T) * ‖w.2.1‖ ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
      rw [e]
      linarith
    have hρ : 0 < ρ := by
      by_contra hneg
      rw [not_lt] at hneg
      have := norm_nonneg w.2.2
      linarith
    have h3 : Real.exp T * ‖w.2.1‖ < ρ :=
      (pow_lt_pow_iff_left₀ (mul_nonneg (Real.exp_pos T).le (norm_nonneg _)) hρ.le
        two_ne_zero).mp h2
    linarith
  · change ‖Real.exp (-s) • w.2.2‖ < ρ
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (-s) * ‖w.2.2‖ ≤ 1 * ‖w.2.2‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < ρ := by rw [one_mul]; exact hy

end

end Finsler.ModelTrap
