module

public import Finsler.Analysis.EquivariantApprox
public import Finsler.Analysis.EquivariantField

/-! Averaging involutive fields preserves descent, compact support and norm bounds. Strictness needs only one strict summand. -/

@[expose] public section

namespace Finsler.EquivariantFieldAverage

open Set Topology Finsler.EquivariantApprox Finsler.EquivariantField

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (τ : E →L[ℝ] E) (hτ : ∀ x, τ (τ x) = x)

include hτ

/-- The directional derivative of the average is the average of two descent derivatives. -/
theorem average_derivative {f : E → ℝ} (hfinv : ∀ x, f (τ x) = f x) (V : E → E)
    {x : E} (hd : DifferentiableAt ℝ f (τ x)) :
    fderiv ℝ f x (average τ τ V x) =
      (1 / 2 : ℝ) * (fderiv ℝ f x (V x) + fderiv ℝ f (τ x) (V (τ x))) := by
  rw [average, map_smul, map_add, smul_eq_mul,
    Finsler.EquivariantField.fderiv_inv τ hτ hfinv hd]

theorem average_nonpos {f : E → ℝ} (hfinv : ∀ x, f (τ x) = f x) (V : E → E)
    {x : E} (hd : DifferentiableAt ℝ f (τ x))
    (hx : fderiv ℝ f x (V x) ≤ 0) (hτx : fderiv ℝ f (τ x) (V (τ x)) ≤ 0) :
    fderiv ℝ f x (average τ τ V x) ≤ 0 := by
  rw [average_derivative τ hτ hfinv V hd]
  linarith

/-- Only one summand needs to descend strictly. -/
theorem average_strict {f : E → ℝ} (hfinv : ∀ x, f (τ x) = f x) (V : E → E)
    {x : E} (hd : DifferentiableAt ℝ f (τ x))
    (hx : fderiv ℝ f x (V x) < 0) (hτx : fderiv ℝ f (τ x) (V (τ x)) ≤ 0) :
    fderiv ℝ f x (average τ τ V x) < 0 := by
  rw [average_derivative τ hτ hfinv V hd]
  linarith

omit hτ in
theorem average_norm_le (hτnorm : ∀ x, ‖τ x‖ ≤ ‖x‖) (V : E → E) {κ : ℝ}
    (hV : ∀ x, ‖V x‖ ≤ κ) (x : E) : ‖average τ τ V x‖ ≤ κ := by
  rw [average, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := norm_add_le (V x) (τ (V (τ x)))
  have h₁ := hτnorm (V (τ x))
  have h₂ := hV x
  have h₃ := hV (τ x)
  linarith

theorem average_hasCompactSupport {V : E → E} (hV : HasCompactSupport V) :
    HasCompactSupport (average τ τ V) := by
  have hconj : HasCompactSupport fun x => τ (V (τ x)) :=
    (hV.comp_homeomorph (invHomeo τ hτ)).comp_left (map_zero τ)
  exact (hV.add hconj).smul_left (f := fun _ => (1 / 2 : ℝ))

/-- The support stays in any invariant set containing the original topological support. -/
theorem average_tsupport_subset {V : E → E} {O : Set E} (hVO : tsupport V ⊆ O)
    (hτO : ∀ x ∈ O, τ x ∈ O) : tsupport (average τ τ V) ⊆ O := by
  have hconj : tsupport (fun x => τ (V (τ x))) ⊆ τ ⁻¹' tsupport V := by
    calc
      tsupport (fun x => τ (V (τ x))) ⊆ tsupport (V ∘ τ) :=
        tsupport_comp_subset (map_zero τ) (V ∘ τ)
      _ ⊆ τ ⁻¹' tsupport V := tsupport_comp_subset_preimage V τ.continuous
  intro x hx
  have hs : x ∈ tsupport (fun x => V x + τ (V (τ x))) :=
    tsupport_smul_subset_right (fun _ => (1 / 2 : ℝ)) (fun x => V x + τ (V (τ x))) hx
  rcases tsupport_add V (fun x => τ (V (τ x))) hs with h₁ | h₂
  · exact hVO h₁
  · have hxτ : τ x ∈ tsupport V := hconj h₂
    have h := hτO (τ x) (hVO hxτ)
    rwa [hτ] at h

end

end Finsler.EquivariantFieldAverage
