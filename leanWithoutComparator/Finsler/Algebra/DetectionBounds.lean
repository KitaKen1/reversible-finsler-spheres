module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! The numerical margins for applying ordinary detection to Gysin iterations.
The ordinary resonance and the actual equivariant restriction maps remain inputs. -/

@[expose] public section

namespace Finsler.DetectionBounds

/-- The injective-side degrees stay above the constant-sphere degrees and below
the ordinary upper margin when C = C_H + α(n-1)D. -/
theorem injective_band (α a D C n j q : ℝ)
    (hα : 0 ≤ α) (hD : 0 ≤ D) (hn : 1 ≤ n)
    (hjHigh : 2 * n + 1 ≤ j)
    (hj : j < α * a - (C + α * (n - 1) * D))
    (hqLow : j - n + 1 ≤ q) (hqHigh : q ≤ j) :
    n + 2 ≤ q ∧ q < α * a - C := by
  have hMargin : 0 ≤ α * (n - 1) * D :=
    mul_nonneg (mul_nonneg hα (sub_nonneg.mpr hn)) hD
  constructor <;> linarith

/-- The zero-side degrees are above the ordinary margin at the largest cut. -/
theorem zero_band (α a D C n j q : ℝ)
    (hj : α * a + (C + α * (n - 1) * D) < j) (hq : j ≤ q) :
    α * (a + (n - 1) * D) + C < q := by nlinarith

end Finsler.DetectionBounds
