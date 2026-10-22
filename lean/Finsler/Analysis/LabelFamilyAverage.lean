module

public import Finsler.Topology.AmbientK

/-! Averaging preserves a compatible family of local fields permuted by reversal and fixed by half-rotation. -/

@[expose] public section

namespace Finsler.LabelFamilyAverage

open Set Finsler.PolygonDescentK Finsler.EquivariantField
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- A group average keeps the prescribed field on each label, even when reversal swaps labels. -/
theorem avg_eq_on_family (r h : E →L[ℝ] E)
    (hr : ∀ x, r (r x) = x) (hh : ∀ x, h (h x) = x)
    (hrh : ∀ x, r (h x) = h (r x)) (rev : ι → ι)
    (T : ι → Set E) (W : ι → E → E) (V : E → E)
    (hTr : ∀ i x, x ∈ T i → r x ∈ T (rev i))
    (hTh : ∀ i x, x ∈ T i → h x ∈ T i)
    (hVW : ∀ i x, x ∈ T i → V x = W i x)
    (hWr : ∀ i x, x ∈ T i → W (rev i) (r x) = r (W i x))
    (hWh : ∀ i x, x ∈ T i → W i (h x) = h (W i x))
    {i : ι} {x : E} (hx : x ∈ T i) : avg r h V x = W i x := by
  have h1 : r (V (r x)) = W i x := by
    rw [hVW _ _ (hTr i x hx), hWr i x hx, hr]
  have h2 : h (V (h x)) = W i x := by
    rw [hVW _ _ (hTh i x hx), hWh i x hx, hh]
  have h3 : r (h (V (r (h x)))) = W i x := by
    rw [hVW _ _ (hTr i (h x) (hTh i x hx)), hWr i (h x) (hTh i x hx),
      hWh i x hx, ← hrh, hr, hh]
  unfold avg
  rw [hVW i x hx, h1, h2, h3]
  module

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A finite sum of label deformations is invariant when the symmetry permutes its terms. -/
theorem sum_invariant [Fintype ι] (r : E → E) (rev : ι ≃ ι) (β : ι → E → ℝ)
    (hβ : ∀ i x, β i (r x) = β (rev i) x) (x : E) :
    (∑ i, β i (r x)) = ∑ i, β i x := by
  simp only [hβ]
  exact Equiv.sum_comp rev (fun i => β i x)

end

end Finsler.LabelFamilyAverage

