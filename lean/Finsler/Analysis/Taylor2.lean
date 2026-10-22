module

public import Mathlib.Analysis.Calculus.MeanValue

/-! A second-order Taylor bound for curves in a normed space. If f has derivative f' and f' has
derivative f'' bounded by M on [0,s], then ‖f'(σ) − f'(0)‖ ≤ Mσ and
‖f(s) − f(0) − s f'(0)‖ ≤ M s². Applied to position and to its derivatives in the initial data,
this gives the quadratic estimates of the exponential map at the zero section. -/

@[expose] public section

namespace Finsler.Taylor2

open Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_sub_le {f' f'' : ℝ → F} {s M : ℝ}
    (hd : ∀ σ ∈ Icc (0 : ℝ) s, HasDerivAt f' (f'' σ) σ) (hM : ∀ σ ∈ Icc (0 : ℝ) s, ‖f'' σ‖ ≤ M)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) s) : ‖f' σ - f' 0‖ ≤ M * σ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f') (f' := f'') (C := M)
    (a := 0) (b := s) (fun x hx => (hd x hx).hasDerivWithinAt)
    (fun x hx => hM x (Ico_subset_Icc_self hx)) σ hσ
  simpa using h

/-- Second-order Taylor bound on [0,s]. -/
theorem taylor_sub_le {f f' f'' : ℝ → F} {s M : ℝ} (hs : 0 ≤ s) (hM0 : 0 ≤ M)
    (hf : ∀ σ ∈ Icc (0 : ℝ) s, HasDerivAt f (f' σ) σ)
    (hd : ∀ σ ∈ Icc (0 : ℝ) s, HasDerivAt f' (f'' σ) σ)
    (hM : ∀ σ ∈ Icc (0 : ℝ) s, ‖f'' σ‖ ≤ M) :
    ‖f s - f 0 - s • f' 0‖ ≤ M * s ^ 2 := by
  let g : ℝ → F := fun σ => f σ - σ • f' 0
  have hg : ∀ σ ∈ Icc (0 : ℝ) s, HasDerivWithinAt g (f' σ - f' 0) (Icc 0 s) σ := by
    intro σ hσ
    have h1 := hf σ hσ
    have h2 : HasDerivAt (fun r : ℝ => r • f' 0) ((1 : ℝ) • f' 0) σ :=
      (hasDerivAt_id σ).smul_const (f' 0)
    rw [one_smul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hb : ∀ σ ∈ Ico (0 : ℝ) s, ‖f' σ - f' 0‖ ≤ M * s := by
    intro σ hσ
    have h := deriv_sub_le hd hM (Ico_subset_Icc_self hσ)
    exact h.trans (mul_le_mul_of_nonneg_left hσ.2.le hM0)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hg hb s (right_mem_Icc.mpr hs)
  have hg0 : g 0 = f 0 := by simp [g]
  have hgs : g s = f s - s • f' 0 := rfl
  rw [hgs, hg0, sub_zero] at h
  calc ‖f s - f 0 - s • f' 0‖ = ‖f s - s • f' 0 - f 0‖ := by congr 1; abel
    _ ≤ M * s * s := h
    _ = M * s ^ 2 := by ring

end Finsler.Taylor2
