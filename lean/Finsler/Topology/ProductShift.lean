module

public import Finsler.Topology.ProductModel
public import Finsler.Topology.LensTrap

/-! The normal shift on a compact band. Let h be a continuous function on a space B with a
descent ψ, let the band {a₀ ≤ h ≤ b₀} be compact, and let W and W' be disjoint open sets such
that the time-one map decreases h strictly at the points of the band outside W ∪ W'. Then there
is d > 0 with the following property. Let a ≤ b be cuts and T ≥ 1 a time, put
ε = (b − a) / (e^{2T} − 1), and suppose that a₀ ≤ a − ε, b + ε ≤ b₀, that the wider cuts differ
by less than d, and that the time-one map decreases h strictly on the strip {b ≤ h ≤ b + ε}.
Then, for every dimension k and normed space V, the lens pair over W of the product model
h(z) − |u|² + |y|² with the flow (ψ_t z, e^t u, e^{-t} y) has the cohomology of the lens pair of
h in W shifted by k. The hypotheses of the normal shift for product models are obtained from
compactness: trapping in W ∪ W' for the wider cuts, its restriction to the piece W, and the
descent across the strip above b. -/

@[expose] public section

namespace Finsler.ProductShift

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.ConeLens Finsler.ProductModel Finsler.LensTrap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {B : TopCat.{0}} {h : B → ℝ} (ψ : Descent B h) (k : ℕ) (V : Type)
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The widening of the cuts is nonnegative. -/
theorem eps_nonneg {a b T : ℝ} (hab : a ≤ b) (hT : 1 ≤ T) :
    0 ≤ (b - a) / (Real.exp (2 * T) - 1) := by
  have hE : 1 < Real.exp (2 * T) := Real.one_lt_exp_iff.mpr (by linarith)
  exact div_nonneg (sub_nonneg.mpr hab) (by linarith)

/-- The normal shift on a compact band: the lens pair of the product model over W has the
cohomology of the lens pair of h in W shifted by k, for tight cuts and T ≥ 1. -/
theorem exists_shift (hh : Continuous h) {a₀ b₀ : ℝ} {Wsel Wrest : Set B} (hsel : IsOpen Wsel)
    (hrest : IsOpen Wrest) (hdis : Disjoint Wsel Wrest)
    (hK : IsCompact {z : B | a₀ ≤ h z ∧ h z ≤ b₀})
    (hstrict : ∀ z, a₀ ≤ h z → h z ≤ b₀ → z ∉ Wsel ∪ Wrest → h (ψ.flow 1 z) < h z) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, 1 ≤ T → a ≤ b →
      a₀ ≤ a - (b - a) / (Real.exp (2 * T) - 1) →
      b + (b - a) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (b + (b - a) / (Real.exp (2 * T) - 1)) - (a - (b - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ z, b ≤ h z → h z ≤ b + (b - a) / (Real.exp (2 * T) - 1) → h (ψ.flow 1 z) < h z) →
      (∀ n, Module.finrank (ZMod 2)
          (H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V Wsel)
            a b T))) (n + k)) =
        Module.finrank (ZMod 2)
          (H (triv (pairOf (inter_subset_left :
            baseP h Wsel b ∩ baseO ψ a T ⊆ baseP h Wsel b))) n)) ∧
      (∀ n, n < k → ∀ z : H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh)
        (over k V Wsel) a b T))) n, z = 0) := by
  obtain ⟨d, hd, htr⟩ := exists_trap ψ hh (hsel.union hrest) hK hstrict
  refine ⟨d, hd, ?_⟩
  intro a b T hT hab ha hb hwidth hstrip
  have hε := eps_nonneg hab hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hPT := htr _ _ T ha hb hwidth hT
  have htrap : ∀ z, z ∈ Wsel → h z < b + (b - a) / (Real.exp (2 * T) - 1) →
      a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T z) → ∀ s, 0 ≤ s →
      a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T (ψ.flow s z)) → ψ.flow s z ∈ Wsel :=
    fun z hz hzb _ s hs hzs => trap_piece ψ hT0.le hsel hrest hdis hPT z hz hzb s hs hzs
  have hKs : IsCompact {z : B | b ≤ h z ∧ h z ≤ b + (b - a) / (Real.exp (2 * T) - 1)} :=
    hK.of_isClosed_subset
      ((isClosed_le continuous_const hh).inter (isClosed_le hh continuous_const))
      (fun z hz => ⟨by linarith [hz.1], hz.2.trans hb⟩)
  obtain ⟨s₀, hs₀, hps⟩ := exists_push ψ hh hKs hstrip
  have hpush : ∀ z, z ∈ Wsel → h z < b + (b - a) / (Real.exp (2 * T) - 1) →
      h (ψ.flow s₀ z) < b := fun z _ hz => hps z hz.le
  exact ⟨fun n => finrank_model hh hsel hT0 hs₀ htrap hpush n,
    fun n hn z => model_eq_zero hh hsel hT0 hs₀ htrap hpush n hn z⟩

end

end Finsler.ProductShift
