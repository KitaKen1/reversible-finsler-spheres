module

public import Finsler.Geometry.RoundModel
public import Finsler.Topology.ConeLens

/-! The model near the regular m-gons as a twisted cone structure.

The model space is V₂ × Fib (pairs z ∈ V₂ with fibre vectors). The scalings act on the negative
part negF = (0, negV z V) and the positive part posF = ξ − negF:

  sc l m (z, ξ) = (z, l negF + m posF),   nn = √sqN,   np = √sqP,   base = (2πm)²,

so the energy base − nn² + np² is the model function. The negative and positive parts depend on
z (the negative bundle of the critical manifold is not trivial), but the cone structure only
needs the scalings and the norms. The flow (z, e^t negF + e^{−t} posF) is a split descent, and the
lens theorem for cone structures identifies the lens pair of the whole model space with the pair
of the negative bundle {sqP = 0} relative to its nonzero vectors {sqP = 0, sqN ≠ 0}. -/

@[expose] public section

namespace Finsler.RoundCone

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundCoords Finsler.RoundSpectral Finsler.RoundPenHess Finsler.AmbientPenalty
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundLabel Finsler.RoundModel
open Finsler.ConeLens Finsler.FlowLens Finsler.RoundModes
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)

/-- The model space. -/
abbrev MS (n N m : ℕ) [NeZero N] : TopCat.{0} :=
  TopCat.of {p : (Ambient n × Ambient n) × Fib n N m // p.1 ∈ V2}

/-- The negative part of a fibre vector. -/
def negF (p : (Ambient n × Ambient n) × Fib n N m) : Fib n N m :=
  (0, ⟨negP p, negV_mem_kern hm hmN p.1 _⟩)

/-- The positive part of a fibre vector. -/
def posF (p : (Ambient n × Ambient n) × Fib n N m) : Fib n N m := p.2 - negF hm hmN p

theorem negF_add_posF (p : (Ambient n × Ambient n) × Fib n N m) :
    negF hm hmN p + posF hm hmN p = p.2 := by
  unfold posF
  abel

theorem coe_negF (p : (Ambient n × Ambient n) × Fib n N m) :
    ((negF hm hmN p).2 : ZMod N → Ambient n) = negP p := rfl

theorem negF_continuous : Continuous (negF (n := n) (N := N) hm hmN) := by
  refine continuous_const.prodMk (Continuous.subtype_mk ?_ _)
  exact (negP_contDiff (n := n) (N := N) (m := m)).continuous

/-! ### The scalings -/

section Scale

variable {z : Ambient n × Ambient n} (hz : z ∈ V2)
include hz

/-- The negative part of a scaled vector. -/
theorem negP_scale (ξ : Fib n N m) (l μ : ℝ) :
    negP (z, l • negF hm hmN (z, ξ) + μ • posF hm hmN (z, ξ)) = l • negP (z, ξ) := by
  unfold negP posF negF
  simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_sub]
  rw [negV_add, negV_smul, negV_smul, negV_sub]
  unfold negP
  rw [negV_negV hmN hz, sub_self, smul_zero, add_zero]

theorem negF_scale (ξ : Fib n N m) (l μ : ℝ) :
    negF hm hmN (z, l • negF hm hmN (z, ξ) + μ • posF hm hmN (z, ξ)) = l • negF hm hmN (z, ξ) := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · simp [negF]
  · rw [coe_negF, negP_scale hm hmN hz]
    rfl

theorem posF_scale (ξ : Fib n N m) (l μ : ℝ) :
    posF hm hmN (z, l • negF hm hmN (z, ξ) + μ • posF hm hmN (z, ξ)) = μ • posF hm hmN (z, ξ) := by
  rw [posF, negF_scale hm hmN hz]
  change l • negF hm hmN (z, ξ) + μ • posF hm hmN (z, ξ) - l • negF hm hmN (z, ξ) = _
  abel

theorem sqN_scale (ξ : Fib n N m) {l : ℝ} (μ : ℝ) :
    sqN (z, l • negF hm hmN (z, ξ) + μ • posF hm hmN (z, ξ)) = l ^ 2 * sqN (z, ξ) := by
  unfold sqN
  rw [negP_scale hm hmN hz, pair_smul_smul]

theorem sqP_scale (ξ : Fib n N m) (l μ : ℝ) :
    sqP (z, l • negF hm hmN (z, ξ) + μ • posF hm hmN (z, ξ)) = μ ^ 2 * sqP (z, ξ) := by
  have hpos := posF_scale hm hmN hz ξ l μ
  have e1 : ∀ ζ : Fib n N m, sqP (z, ζ) = (posF hm hmN (z, ζ)).1.1 ^ 2 +
      (posF hm hmN (z, ζ)).1.2.1 ^ 2 + (posF hm hmN (z, ζ)).1.2.2 ^ 2 +
      pair ((posF hm hmN (z, ζ)).2 : ZMod N → Ambient n)
        ((posF hm hmN (z, ζ)).2 : ZMod N → Ambient n) := by
    intro ζ
    unfold sqP posF negF
    simp
  rw [e1, e1, hpos]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Submodule.coe_smul, pair_smul_smul]
  ring

end Scale

/-- The scaling of the model space. -/
def scM (l μ : ℝ) (w : MS n N m) : MS n N m :=
  ⟨(w.1.1, l • negF hm hmN w.1 + μ • posF hm hmN w.1), w.2⟩

theorem scM_comp (w : MS n N m) (l μ l' μ' : ℝ) :
    scM hm hmN l μ (scM hm hmN l' μ' w) = scM hm hmN (l * l') (μ * μ') w := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change l • negF hm hmN (w.1.1, l' • negF hm hmN w.1 + μ' • posF hm hmN w.1) +
      μ • posF hm hmN (w.1.1, l' • negF hm hmN w.1 + μ' • posF hm hmN w.1) =
    (l * l') • negF hm hmN w.1 + (μ * μ') • posF hm hmN w.1
  rw [negF_scale hm hmN w.2, posF_scale hm hmN w.2, smul_smul, smul_smul]

theorem scM_one (w : MS n N m) : scM hm hmN 1 1 w = w := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change (1 : ℝ) • negF hm hmN w.1 + (1 : ℝ) • posF hm hmN w.1 = w.1.2
  rw [one_smul, one_smul, negF_add_posF]

theorem scM_continuous : Continuous fun p : (ℝ × ℝ) × MS n N m => scM hm hmN p.1.1 p.1.2 p.2 := by
  have hw : Continuous fun p : (ℝ × ℝ) × MS n N m => (p.2 : (Ambient n × Ambient n) × Fib n N m) :=
    continuous_subtype_val.comp continuous_snd
  have hn : Continuous fun p : (ℝ × ℝ) × MS n N m => negF hm hmN p.2.1 :=
    (negF_continuous hm hmN).comp hw
  have hp : Continuous fun p : (ℝ × ℝ) × MS n N m => posF hm hmN p.2.1 :=
    (continuous_snd.comp hw).sub hn
  refine Continuous.subtype_mk ((continuous_fst.comp hw).prodMk ?_) _
  exact ((continuous_fst.comp continuous_fst).smul hn).add ((continuous_snd.comp continuous_fst).smul hp)

/-- The twisted cone structure of the model. -/
def cone : Cone (MS n N m) where
  sc := scM hm hmN
  cont := scM_continuous hm hmN
  one := scM_one hm hmN
  nn w := Real.sqrt (sqN w.1)
  np w := Real.sqrt (sqP w.1)
  base _ := (2 * π * m) ^ 2
  nn_cont := Real.continuous_sqrt.comp
    ((sqN_contDiff (n := n) (N := N) (m := m)).continuous.comp continuous_subtype_val)
  np_cont := Real.continuous_sqrt.comp
    ((sqP_contDiff (n := n) (N := N) (m := m)).continuous.comp continuous_subtype_val)
  base_cont := continuous_const
  nn_nonneg _ := Real.sqrt_nonneg _
  np_nonneg _ := Real.sqrt_nonneg _
  nn_sc l μ w hl _ := by
    change Real.sqrt (sqN (w.1.1, l • negF hm hmN w.1 + μ • posF hm hmN w.1)) = l * _
    rw [sqN_scale hm hmN w.2, Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq hl]
  np_sc l μ w _ hμ := by
    change Real.sqrt (sqP (w.1.1, l • negF hm hmN w.1 + μ • posF hm hmN w.1)) = μ * _
    rw [sqP_scale hm hmN w.2, Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ]
  base_sc _ _ _ _ _ := rfl
  nn_zero w hw := by
    have h0 : sqN w.1 = 0 := by
      have := Real.sqrt_eq_zero (sqN_nonneg w.1) |>.mp hw
      exact this
    have hA : negP w.1 = 0 := pair_eq_zero h0
    have hnegF : negF hm hmN w.1 = 0 := Prod.ext rfl (Subtype.ext hA)
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change (0 : ℝ) • negF hm hmN w.1 + (1 : ℝ) • posF hm hmN w.1 = w.1.2
    rw [zero_smul, zero_add, one_smul, posF, hnegF, sub_zero]

theorem cone_energy (w : MS n N m) : (cone hm hmN).energy w = model m w.1 := by
  change (2 * π * m) ^ 2 - Real.sqrt (sqN w.1) ^ 2 + Real.sqrt (sqP w.1) ^ 2 = model m w.1
  rw [Real.sq_sqrt (sqN_nonneg _), Real.sq_sqrt (sqP_nonneg _)]
  rfl

/-! ### The split descent -/

/-- The model flow. -/
def flowM (t : ℝ) (w : MS n N m) : MS n N m := scM hm hmN (Real.exp t) (Real.exp (-t)) w

/-- The split descent of the model. -/
def descentM : Descent (MS n N m) (cone hm hmN).energy where
  flow := flowM hm hmN
  cont := by
    have h := scM_continuous (n := n) (N := N) hm hmN
    exact h.comp (((Real.continuous_exp.comp continuous_fst).prodMk
      (Real.continuous_exp.comp continuous_fst.neg)).prodMk continuous_snd)
  zero w := by
    change scM hm hmN (Real.exp 0) (Real.exp (-0)) w = w
    rw [neg_zero, Real.exp_zero, scM_one]
  add s t w _ _ := by
    change scM hm hmN (Real.exp (s + t)) (Real.exp (-(s + t))) w =
      scM hm hmN (Real.exp s) (Real.exp (-s)) (scM hm hmN (Real.exp t) (Real.exp (-t)) w)
    rw [scM_comp, ← Real.exp_add, ← Real.exp_add, neg_add]
  mono t w ht := by
    rw [cone_energy, cone_energy]
    change model m (w.1.1, Real.exp t • negF hm hmN w.1 + Real.exp (-t) • posF hm hmN w.1) ≤
      model m w.1
    unfold model
    rw [sqN_scale hm hmN w.2, sqP_scale hm hmN w.2]
    have h1 : 1 ≤ Real.exp t ^ 2 := one_le_pow₀ (Real.one_le_exp ht)
    have h2 : Real.exp (-t) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
    have hN := sqN_nonneg w.1
    have hP := sqP_nonneg w.1
    nlinarith

theorem split : Split (cone (n := n) (N := N) hm hmN) (descentM (n := n) (N := N) hm hmN) where
  comm t l μ w _ _ _ := by
    change scM hm hmN (Real.exp t) (Real.exp (-t)) (scM hm hmN l μ w) =
      scM hm hmN l μ (scM hm hmN (Real.exp t) (Real.exp (-t)) w)
    rw [scM_comp, scM_comp, mul_comm (Real.exp t), mul_comm (Real.exp (-t))]
  nn_flow t w ht := by
    change Real.sqrt (sqN w.1) ≤ Real.sqrt (sqN (w.1.1, Real.exp t • negF hm hmN w.1 +
      Real.exp (-t) • posF hm hmN w.1))
    rw [sqN_scale hm hmN w.2]
    apply Real.sqrt_le_sqrt
    have h1 : 1 ≤ Real.exp t ^ 2 := one_le_pow₀ (Real.one_le_exp ht)
    nlinarith [sqN_nonneg w.1]
  np_flow t w ht := by
    change Real.sqrt (sqP (w.1.1, Real.exp t • negF hm hmN w.1 +
      Real.exp (-t) • posF hm hmN w.1)) ≤ Real.sqrt (sqP w.1)
    rw [sqP_scale hm hmN w.2]
    apply Real.sqrt_le_sqrt
    have h2 : Real.exp (-t) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
    nlinarith [sqP_nonneg w.1]
  base_flow _ _ _ := le_rfl

end

end Finsler.RoundCone
