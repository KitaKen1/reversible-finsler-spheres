module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-! A single tight-cut width controls all product-flow widenings at times at least one. -/

@[expose] public section

namespace Finsler.WidenedCuts

theorem exists_width {a₀ b₀ c d : ℝ} (ha : a₀ < c) (hb : c < b₀) (hd : 0 < d) :
    ∃ e : ℝ, 0 < e ∧ ∀ l u T : ℝ, 1 ≤ T → l < c → c < u → u - l < e →
      a₀ ≤ l - (u - l) / (Real.exp (2 * T) - 1) ∧
      u + (u - l) / (Real.exp (2 * T) - 1) ≤ b₀ ∧
      (u + (u - l) / (Real.exp (2 * T) - 1)) -
        (l - (u - l) / (Real.exp (2 * T) - 1)) < d := by
  refine ⟨min ((c - a₀) / 2) (min ((b₀ - c) / 2) (d / 2)),
    lt_min (by linarith) (lt_min (by linarith) (by linarith)),
    fun l u T hT hl hu hw => ?_⟩
  have hw₁ := hw.trans_le (min_le_left _ _)
  have hw₂ := hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hw₃ := hw.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hE : 2 ≤ Real.exp (2 * T) - 1 := by
    have h1 : 2 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have h2 : Real.exp 2 ≤ Real.exp (2 * T) := Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith
  have hε : 2 * ((u - l) / (Real.exp (2 * T) - 1)) ≤ u - l := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  exact ⟨by linarith, by linarith, by linarith⟩

end Finsler.WidenedCuts
