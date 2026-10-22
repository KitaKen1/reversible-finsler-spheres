module

public import Finsler.Analysis.EquivariantFieldAverage

/-! The four-element average as two successive involution averages. Smoothness, compact
support and descent are preserved. Strict descent at the original point suffices; the other
three translates only need nonpositive derivatives. -/

@[expose] public section

namespace Finsler.EquivariantGroupAverage

open Set Finsler.EquivariantField Finsler.EquivariantApprox Finsler.EquivariantFieldAverage
open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (r h : E →L[ℝ] E) (hr : ∀ x, r (r x) = x) (hh : ∀ x, h (h x) = x)
  (hrh : ∀ x, r (h x) = h (r x))

include hrh

theorem avg_eq_iterated (V : E → E) : avg r h V = average r r (average h h V) := by
  funext x
  simp only [avg, average, map_smul, map_add]
  rw [← hrh x]
  module

theorem avg_contDiff {V : E → E} (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (avg r h V) := by
  rw [avg_eq_iterated r h hrh]
  exact average_contDiff r r (average_contDiff h h hV)

include hr hh

theorem avg_hasCompactSupport {V : E → E} (hV : HasCompactSupport V) :
    HasCompactSupport (avg r h V) := by
  rw [avg_eq_iterated r h hrh]
  exact average_hasCompactSupport r hr (average_hasCompactSupport h hh hV)

theorem avg_tsupport_subset {V : E → E} {O : Set E} (hVO : tsupport V ⊆ O)
    (hOr : ∀ x ∈ O, r x ∈ O) (hOh : ∀ x ∈ O, h x ∈ O) : tsupport (avg r h V) ⊆ O := by
  rw [avg_eq_iterated r h hrh]
  exact average_tsupport_subset r hr (average_tsupport_subset h hh hVO hOh) hOr

theorem avg_derivative {f : E → ℝ} (hfr : ∀ x, f (r x) = f x) (hfh : ∀ x, f (h x) = f x)
    {O : Set E} (hd : ∀ x ∈ O, DifferentiableAt ℝ f x)
    (hOr : ∀ x ∈ O, r x ∈ O) (hOh : ∀ x ∈ O, h x ∈ O)
    (V : E → E) {x : E} (hx : x ∈ O) :
    fderiv ℝ f x (avg r h V x) = (1 / 4 : ℝ) *
      (fderiv ℝ f x (V x) + fderiv ℝ f (r x) (V (r x)) +
        fderiv ℝ f (h x) (V (h x)) + fderiv ℝ f (r (h x)) (V (r (h x)))) := by
  rw [avg_eq_iterated r h hrh,
    average_derivative r hr hfr _ (hd _ (hOr x hx)),
    average_derivative h hh hfh _ (hd _ (hOh x hx)),
    average_derivative h hh hfh _ (hd _ (hOh _ (hOr x hx))), ← hrh x]
  ring

theorem avg_nonpos_on {f : E → ℝ} (hfr : ∀ x, f (r x) = f x) (hfh : ∀ x, f (h x) = f x)
    {O : Set E} (hd : ∀ x ∈ O, DifferentiableAt ℝ f x)
    (hOr : ∀ x ∈ O, r x ∈ O) (hOh : ∀ x ∈ O, h x ∈ O)
    {V : E → E} (hle : ∀ x ∈ O, fderiv ℝ f x (V x) ≤ 0) {x : E} (hx : x ∈ O) :
    fderiv ℝ f x (avg r h V x) ≤ 0 := by
  rw [avg_derivative r h hr hh hrh hfr hfh hd hOr hOh V hx]
  have h1 := hle x hx
  have h2 := hle _ (hOr x hx)
  have h3 := hle _ (hOh x hx)
  have h4 := hle _ (hOr _ (hOh x hx))
  linarith

/-- No invariance of the strict-descent subset is required. -/
theorem avg_strict_of_nonpos {f : E → ℝ}
    (hfr : ∀ x, f (r x) = f x) (hfh : ∀ x, f (h x) = f x)
    {O : Set E} (hd : ∀ x ∈ O, DifferentiableAt ℝ f x)
    (hOr : ∀ x ∈ O, r x ∈ O) (hOh : ∀ x ∈ O, h x ∈ O)
    {V : E → E} (hle : ∀ x ∈ O, fderiv ℝ f x (V x) ≤ 0)
    {x : E} (hx : x ∈ O) (hlt : fderiv ℝ f x (V x) < 0) :
    fderiv ℝ f x (avg r h V x) < 0 := by
  rw [avg_derivative r h hr hh hrh hfr hfh hd hOr hOh V hx]
  have h2 := hle _ (hOr x hx)
  have h3 := hle _ (hOh x hx)
  have h4 := hle _ (hOr _ (hOh x hx))
  linarith

end

end Finsler.EquivariantGroupAverage
