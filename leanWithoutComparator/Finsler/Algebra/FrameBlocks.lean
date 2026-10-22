module

public import Finsler.Analysis.InvolutionIndex
public import Finsler.Analysis.CurveEquivFrames
public import Mathlib.Data.Fin.Tuple.Basic

/-! Concatenation of definite frame blocks and signed eigenframes. -/

@[expose] public section

namespace Finsler.FrameBlocks

open Set QuadraticMap Finsler.DefiniteFrames Finsler.InvolutionIndex Finsler.CurveEquivFrames

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {b p : ℕ}

theorem comb_append (G : Fin b → V) (H : Fin p → V) (u : Fin (b + p) → ℝ) :
    comb (Fin.append G H) u =
      comb G (fun i => u (Fin.castAdd p i)) + comb H (fun i => u (Fin.natAdd b i)) := by
  simp only [comb, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- Orthogonal negative blocks concatenate to a negative frame. -/
theorem neg_append (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ v w, β v w = β w v)
    {G : Fin b → V} {H : Fin p → V} (hG : Neg β G) (hH : Neg β H)
    (horth : ∀ i j, β (G i) (H j) = 0) : Neg β (Fin.append G H) := by
  intro u hu
  let u₁ : Fin b → ℝ := fun i => u (Fin.castAdd p i)
  let u₂ : Fin p → ℝ := fun i => u (Fin.natAdd b i)
  have hc : β (comb G u₁) (comb H u₂) = 0 := by
    apply form_comb_left_eq_zero β G
    intro i
    rw [hsym]
    exact form_comb_left_eq_zero β H (fun j => by rw [hsym]; exact horth i j) u₂
  have hc' : β (comb H u₂) (comb G u₁) = 0 := by rw [hsym]; exact hc
  have he : β (comb (Fin.append G H) u) (comb (Fin.append G H) u) =
      β (comb G u₁) (comb G u₁) + β (comb H u₂) (comb H u₂) := by
    rw [comb_append]
    change β (comb G u₁ + comb H u₂) (comb G u₁ + comb H u₂) = _
    simp only [map_add, LinearMap.add_apply, hc, hc', add_zero, zero_add]
  have hz₁ : u₁ = 0 → β (comb G u₁) (comb G u₁) = 0 := by
    intro h; simp [h, comb]
  have hz₂ : u₂ = 0 → β (comb H u₂) (comb H u₂) = 0 := by
    intro h; simp [h, comb]
  have hne : u₁ ≠ 0 ∨ u₂ ≠ 0 := by
    by_contra hn
    simp only [not_or, not_not] at hn
    apply hu
    funext i
    refine Fin.addCases (fun j => congrFun hn.1 j) (fun j => congrFun hn.2 j) i
  rw [he]
  rcases hne with h₁ | h₂
  · have h₁' := hG u₁ h₁
    by_cases h₂ : u₂ = 0
    · rw [hz₂ h₂, add_zero]; exact h₁'
    · linarith [hH u₂ h₂]
  · have h₂' := hH u₂ h₂
    by_cases h₁ : u₁ = 0
    · rw [hz₁ h₁, zero_add]; exact h₂'
    · linarith [hG u₁ h₁]

/-- View a frame in either eigenspace as an ambient frame. -/
theorem neg_eigen_coe (T : Module.End ℝ V) (e : ℝ) (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    {G : Fin b → T.eigenspace e} (hG : Neg (eigenForm T e β) G) :
    Neg β (fun i => (G i : V)) := by
  intro u hu
  have h := hG u hu
  have hc : ((comb G u : T.eigenspace e) : V) = comb (fun i => (G i : V)) u := by
    simp only [comb, Submodule.coe_sum, Submodule.coe_smul]
  change β ((comb G u : T.eigenspace e) : V) ((comb G u : T.eigenspace e) : V) < 0 at h
  rwa [hc] at h

/-- Opposite involution eigenspaces give the required orthogonal blocks. -/
theorem neg_eigen_append (T : Module.End ℝ V) (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, β v w = β w v) (hinv : ∀ v w, β (T v) (T w) = β v w)
    {G : Fin b → T.eigenspace 1} {H : Fin p → T.eigenspace (-1)}
    (hG : Neg (eigenForm T 1 β) G) (hH : Neg (eigenForm T (-1) β) H) :
    Neg β (Fin.append (fun i => (G i : V)) (fun i => (H i : V))) := by
  exact neg_append β hsym (neg_eigen_coe T 1 β hG) (neg_eigen_coe T (-1) β hH)
    (fun i j => eigenspaces_orthogonal T β hinv (G i) (H j))

/-- The signed action fixes the concatenated positive and negative eigenspace frames. -/
theorem signAction_eigen_append (T : V →L[ℝ] V)
    (G : Fin b → Module.End.eigenspace T.toLinearMap 1)
    (H : Fin p → Module.End.eigenspace T.toLinearMap (-1)) :
    signAction T (Fin.append (fun _ : Fin b => (1 : ℝ)) (fun _ : Fin p => (-1 : ℝ)))
      (Fin.append (fun i => (G i : V)) (fun i => (H i : V))) =
        Fin.append (fun i => (G i : V)) (fun i => (H i : V)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [signAction_apply, Fin.append_left, one_smul]
    exact (Module.End.mem_eigenspace_iff.mp (G j).2).trans (one_smul _ _)
  · simp only [signAction_apply, Fin.append_right, neg_one_smul]
    have h : T (H j : V) = -(H j : V) :=
      (Module.End.mem_eigenspace_iff.mp (H j).2).trans (neg_one_smul _ _)
    rw [h, neg_neg]

omit [NormedSpace ℝ V] in
theorem continuous_append {Θ : Type*} [TopologicalSpace Θ]
    {G : Θ → Fin b → V} {H : Θ → Fin p → V} (hG : Continuous G) (hH : Continuous H) :
    Continuous fun θ => Fin.append (G θ) (H θ) := by
  apply continuous_pi
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left, Function.comp_def] using (continuous_apply j).comp hG
  · simpa only [Fin.append_right, Function.comp_def] using (continuous_apply j).comp hH

/-- Complementary negative and positive frames determine the full negative index. -/
theorem sigNeg_eq_of_complementary [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ v w, β v w = β w v)
    (hker : LinearMap.ker β = ⊥) {G : Fin b → V}
    {H : Fin (Module.finrank ℝ V - b) → V} (hG : Neg β G) (hH : Neg (-β) H) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap β) = b := by
  have h₁ := Finsler.FormSemicontinuity.le_sigNeg_of_neg hG
  have h₂ := Finsler.FormSemicontinuity.le_sigNeg_of_neg hH
  rw [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg] at h₂
  have hsum := Finsler.FormSemicontinuity.sigPos_add_sigNeg_add_ker hsym
  rw [hker, finrank_bot, add_zero] at hsum
  omega

end

end Finsler.FrameBlocks
