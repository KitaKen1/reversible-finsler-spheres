module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Pseudo-gradient fields. Let f be a C¹ function on an open set O of a finite-dimensional
normed space and A a compact subset of O on which the derivative of f does not vanish. Then
there is a smooth vector field V with compact support in O such that the derivative of f in
the direction V is nonpositive on O and negative on A. Around every point x of A a constant
vector v_x decreases f on a ball, by continuity of the derivative; finitely many of the balls
of half the radius cover A, and V is the sum of the vectors v_x multiplied by bump functions
which are 1 on the smaller and supported in the larger balls. No partition of unity and no
Lipschitz bound for the derivative of f is needed. -/

@[expose] public section

namespace Finsler.PseudoGradient

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Near a point of an open set where the derivative of a C¹ function does not vanish, a
constant vector decreases the function. -/
theorem exists_descent_vector {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 f O) {x : E} (hx : x ∈ O) (hne : fderiv ℝ f x ≠ 0) :
    ∃ v : E, ∃ ρ : ℝ, 0 < ρ ∧ closedBall x (2 * ρ) ⊆ O ∧
      ∀ y ∈ closedBall x (2 * ρ), fderiv ℝ f y v < 0 := by
  obtain ⟨w, hw⟩ : ∃ w : E, fderiv ℝ f x w ≠ 0 := by
    by_contra h
    apply hne
    ext w
    by_contra hw
    exact h ⟨w, hw⟩
  obtain ⟨v, hv⟩ : ∃ v : E, fderiv ℝ f x v < 0 := by
    rcases lt_or_gt_of_ne hw with h | h
    · exact ⟨w, h⟩
    · exact ⟨-w, by rw [map_neg]; linarith⟩
  have hc : ContinuousOn (fun y => fderiv ℝ f y v) O :=
    (hf.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have hopen : IsOpen (O ∩ {y | fderiv ℝ f y v < 0}) := by
    have h := hc.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
    exact h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨hx, hv⟩
  refine ⟨v, ε / 4, by positivity, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ ball x ε := by
      rw [mem_closedBall] at hy
      rw [mem_ball]
      linarith
    exact (hball hy').1
  · intro y hy
    have hy' : y ∈ ball x ε := by
      rw [mem_closedBall] at hy
      rw [mem_ball]
      linarith
    exact (hball hy').2

/-- A bump function for a centre and a radius: 1 on the closed ball of the radius, supported in
the ball of twice the radius; zero if the radius is not positive. -/
def bump (x : E) (ρ : ℝ) (y : E) : ℝ :=
  if h : 0 < ρ then (⟨ρ, 2 * ρ, h, by linarith⟩ : ContDiffBump x) y else 0

theorem bump_nonneg (x : E) (ρ : ℝ) (y : E) : 0 ≤ bump x ρ y := by
  unfold bump
  split_ifs with h
  · exact ContDiffBump.nonneg _
  · exact le_rfl

theorem bump_eq_one {x : E} {ρ : ℝ} (h : 0 < ρ) {y : E} (hy : y ∈ closedBall x ρ) :
    bump x ρ y = 1 := by
  unfold bump
  rw [dite_eq_left h]
  exact ContDiffBump.one_of_mem_closedBall _ hy

theorem bump_eq_zero {x : E} {ρ : ℝ} {y : E} (hy : y ∉ ball x (2 * ρ)) : bump x ρ y = 0 := by
  unfold bump
  split_ifs with h
  · have hs := ContDiffBump.support_eq (⟨ρ, 2 * ρ, h, by linarith⟩ : ContDiffBump x)
    by_contra hne
    apply hy
    rw [← hs]
    exact hne
  · rfl

theorem bump_contDiff (x : E) (ρ : ℝ) : ContDiff ℝ ∞ (bump x ρ) := by
  by_cases h : 0 < ρ
  · have he : bump x ρ = fun y => (⟨ρ, 2 * ρ, h, by linarith⟩ : ContDiffBump x) y := by
      funext y
      unfold bump
      rw [dite_eq_left h]
    rw [he]
    exact ContDiffBump.contDiff _
  · have he : bump x ρ = fun _ => (0 : ℝ) := by
      funext y
      unfold bump
      rw [dite_eq_right h]
    rw [he]
    exact contDiff_const

/-- Pseudo-gradient: a smooth field with compact support in O along which f does not increase
on O and decreases strictly on a compact set on which the derivative of f does not vanish. -/
theorem exists_pseudoGradient {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 f O) {A : Set E} (hA : IsCompact A) (hAO : A ⊆ O)
    (hne : ∀ x ∈ A, fderiv ℝ f x ≠ 0) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ O ∧
      (∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) ∧ ∀ y ∈ A, fderiv ℝ f y (V y) < 0 := by
  have hex : ∀ x : E, ∃ v : E, ∃ ρ : ℝ, x ∈ A → (0 < ρ ∧ closedBall x (2 * ρ) ⊆ O ∧
      ∀ y ∈ closedBall x (2 * ρ), fderiv ℝ f y v < 0) := by
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨v, ρ, h⟩ := exists_descent_vector hO hf (hAO hx) (hne x hx)
      exact ⟨v, ρ, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hx⟩
  choose v ρ hvρ using hex
  obtain ⟨t, htA, hcov⟩ := hA.elim_nhds_subcover (fun x => ball x (ρ x))
    (fun x hx => ball_mem_nhds x (hvρ x hx).1)
  set V : E → E := fun y => ∑ x ∈ t, bump x (ρ x) y • v x with hV
  have hterm : ∀ x ∈ t, ∀ y ∈ O, bump x (ρ x) y * fderiv ℝ f y (v x) ≤ 0 := by
    intro x hx y _
    by_cases hy : y ∈ ball x (2 * ρ x)
    · exact mul_nonpos_of_nonneg_of_nonpos (bump_nonneg _ _ _)
        ((hvρ x (htA x hx)).2.2 y (ball_subset_closedBall hy)).le
    · rw [bump_eq_zero hy, zero_mul]
  have hsum : ∀ y, fderiv ℝ f y (V y) = ∑ x ∈ t, bump x (ρ x) y * fderiv ℝ f y (v x) := by
    intro y
    rw [hV, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_smul, smul_eq_mul]
  have hK : IsCompact (⋃ x ∈ t, closedBall x (2 * ρ x)) :=
    t.finite_toSet.isCompact_biUnion fun x _ => isCompact_closedBall x (2 * ρ x)
  have hzero : ∀ y, y ∉ ⋃ x ∈ t, closedBall x (2 * ρ x) → V y = 0 := by
    intro y hy
    rw [hV]
    apply Finset.sum_eq_zero
    intro x hx
    have hyb : y ∉ ball x (2 * ρ x) := fun h =>
      hy (mem_biUnion hx (ball_subset_closedBall h))
    rw [bump_eq_zero hyb, zero_smul]
  have hKO : (⋃ x ∈ t, closedBall x (2 * ρ x)) ⊆ O :=
    iUnion₂_subset fun x hx => (hvρ x (htA x hx)).2.1
  refine ⟨V, ?_, HasCompactSupport.intro hK hzero, ?_, ?_, ?_⟩
  · rw [hV]
    exact ContDiff.sum fun x _ => (bump_contDiff x (ρ x)).smul contDiff_const
  · have hsub : Function.support V ⊆ ⋃ x ∈ t, closedBall x (2 * ρ x) := by
      intro y hy
      by_contra h
      exact hy (hzero y h)
    exact (closure_minimal hsub hK.isClosed).trans hKO
  · intro y hy
    rw [hsum]
    exact Finset.sum_nonpos fun x hx => hterm x hx y hy
  · intro y hy
    rw [hsum]
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcov hy)
    apply Finset.sum_neg' (fun x hx => hterm x hx y (hAO hy))
    refine ⟨x, hx, ?_⟩
    rw [bump_eq_one (hvρ x (htA x hx)).1 (ball_subset_closedBall hyx), one_mul]
    have h2 : y ∈ closedBall x (2 * ρ x) := by
      have hρ := (hvρ x (htA x hx)).1
      rw [mem_ball] at hyx
      rw [mem_closedBall]
      linarith
    exact (hvρ x (htA x hx)).2.2 y h2

end

end Finsler.PseudoGradient
