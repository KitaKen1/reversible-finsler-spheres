module

public import TauCeti.Analysis.Normed.Algebra.SquareRoot
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Congruence of a family of symmetric operators with an invertible one, with parameters and
finite regularity. Let `S w` be symmetric operators on a real Hilbert space depending `C^k` on a
parameter `w` near `w₀`, with `S w₀ = S₀` invertible. Then there are operators `R w`, `C^k` at
`w₀` with `R w₀ = 1`, such that `⟪S₀ (R w x), R w x'⟫ = ⟪S w x, x'⟫` near `w₀`. The operator
`R w` is the square root near the identity (Tau Ceti) of `S₀⁻¹ S w`; it is self-adjoint for the
pairing `⟪S₀ ·, ·⟫` because the square root near the identity is unique. For the same reason
`R w` commutes with every invertible operator that commutes with all `S w`. This is the linear
part of a Morse lemma with parameters; the family need not be smooth and the parameter space is
arbitrary. -/

@[expose] public section

namespace Finsler.Congruence

open Filter TauCeti
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section

section Sqrt

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A map that fixes `1`, is continuous at `1` and preserves squares fixes the square root near
`1` of every element near `1` that it fixes. -/
theorem eventually_map_sqrtNearOne {Φ : A → A} (h1 : Φ 1 = 1) (hc : ContinuousAt Φ 1)
    (hsq : ∀ a, Φ (a * a) = Φ a * Φ a) :
    ∀ᶠ c in 𝓝 (1 : A), Φ c = c → Φ (sqrtNearOne A c) = sqrtNearOne A c := by
  have hcont : ContinuousAt (fun c => Φ (sqrtNearOne A c)) 1 :=
    hc.comp_of_eq continuousAt_sqrtNearOne sqrtNearOne_one
  have ht : Tendsto (fun c => Φ (sqrtNearOne A c)) (𝓝 1) (𝓝 1) := by
    have h : Tendsto (fun c => Φ (sqrtNearOne A c)) (𝓝 1) (𝓝 (Φ (sqrtNearOne A 1))) :=
      hcont.tendsto
    rwa [sqrtNearOne_one, h1] at h
  filter_upwards [ht.eventually eventually_sqrtNearOne_mul_self,
    eventually_mul_self_sqrtNearOne] with c h2 h3 hΦ
  rw [← hsq, h3, hΦ] at h2
  exact h2.symm

end Sqrt

variable {W N : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]

/-- The adjoint of an operator for the pairing `⟪S₀ ·, ·⟫`. -/
def adj (S₀ : N ≃L[ℝ] N) (T : N →L[ℝ] N) : N →L[ℝ] N :=
  (S₀.symm : N →L[ℝ] N).comp ((ContinuousLinearMap.adjoint T).comp (S₀ : N →L[ℝ] N))

theorem adj_spec (S₀ : N ≃L[ℝ] N) (T : N →L[ℝ] N) (x x' : N) :
    ⟪S₀ (adj S₀ T x), x'⟫ = ⟪S₀ x, T x'⟫ := by
  change ⟪S₀ (S₀.symm (ContinuousLinearMap.adjoint T (S₀ x))), x'⟫ = ⟪S₀ x, T x'⟫
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace N] in
/-- An operator is determined by the pairing `⟪S₀ ·, ·⟫`. -/
theorem eq_of_pairing (S₀ : N ≃L[ℝ] N) {T₁ T₂ : N →L[ℝ] N}
    (h : ∀ x x', ⟪S₀ (T₁ x), x'⟫ = ⟪S₀ (T₂ x), x'⟫) : T₁ = T₂ :=
  ContinuousLinearMap.ext fun x => S₀.injective (ext_inner_right ℝ (h x))

theorem adj_one (S₀ : N ≃L[ℝ] N) : adj S₀ 1 = 1 :=
  eq_of_pairing S₀ fun x x' => by
    rw [adj_spec]
    rfl

theorem adj_mul (S₀ : N ≃L[ℝ] N) (S T : N →L[ℝ] N) : adj S₀ (S * T) = adj S₀ T * adj S₀ S :=
  eq_of_pairing S₀ fun x x' => by
    rw [adj_spec]
    change ⟪S₀ x, S (T x')⟫ = ⟪S₀ (adj S₀ T (adj S₀ S x)), x'⟫
    rw [adj_spec, adj_spec]

theorem continuous_adj (S₀ : N ≃L[ℝ] N) : Continuous (adj S₀) :=
  continuous_const.clm_comp
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := N) (F := N)).continuous.clm_comp
      continuous_const)

/-- Congruence of a `C^k` family of symmetric operators with its invertible value at `w₀`. The
congruence operators commute with every invertible operator commuting with the family. -/
theorem exists_congruence {S : W → N →L[ℝ] N} {w₀ : W} {k : WithTop ℕ∞}
    (hS : ContDiffAt ℝ k S w₀) (hsymm : ∀ᶠ w in 𝓝 w₀, ∀ x x', ⟪S w x, x'⟫ = ⟪x, S w x'⟫)
    (S₀ : N ≃L[ℝ] N) (hS₀ : (S₀ : N →L[ℝ] N) = S w₀) :
    ∃ R : W → N →L[ℝ] N, ContDiffAt ℝ k R w₀ ∧ R w₀ = 1 ∧
      (∀ᶠ w in 𝓝 w₀, ∀ x x', ⟪S₀ (R w x), R w x'⟫ = ⟪S w x, x'⟫) ∧
      ∀ J : N ≃L[ℝ] N, (∀ᶠ w in 𝓝 w₀, ∀ x, S w (J x) = J (S w x)) →
        ∀ᶠ w in 𝓝 w₀, ∀ x, R w (J x) = J (R w x) := by
  have hS₀x : ∀ x, S₀ x = S w₀ x := fun x =>
    congrArg (fun T : N →L[ℝ] N => T x) hS₀
  have hsymm₀ : ∀ x x', ⟪S₀ x, x'⟫ = ⟪x, S₀ x'⟫ := by
    intro x x'
    rw [hS₀x, hS₀x]
    exact hsymm.self_of_nhds x x'
  set C : W → N →L[ℝ] N := fun w => (S₀.symm : N →L[ℝ] N).comp (S w) with hCdef
  have hCapply : ∀ w x, S₀ (C w x) = S w x := fun w x => S₀.apply_symm_apply _
  have hC0 : C w₀ = 1 := by
    refine ContinuousLinearMap.ext fun x => ?_
    change S₀.symm (S w₀ x) = x
    rw [← hS₀x]
    exact S₀.symm_apply_apply x
  have hCk : ContDiffAt ℝ k C w₀ := contDiffAt_const.clm_comp hS
  have hCt : Tendsto C (𝓝 w₀) (𝓝 1) := by
    have h := hCk.continuousAt.tendsto
    rwa [hC0] at h
  refine ⟨fun w => sqrtNearOne (N →L[ℝ] N) (C w), ?_, ?_, ?_, ?_⟩
  · have h : ContDiffAt ℝ k (sqrtNearOne (N →L[ℝ] N)) (C w₀) := by
      rw [hC0]
      exact analyticAt_sqrtNearOne.contDiffAt
    exact h.comp w₀ hCk
  · change sqrtNearOne (N →L[ℝ] N) (C w₀) = 1
    rw [hC0, sqrtNearOne_one]
  · have hadj := hCt.eventually (eventually_map_sqrtNearOne (Φ := adj S₀) (adj_one S₀)
      (continuous_adj S₀).continuousAt (fun a => adj_mul S₀ a a))
    have hsq := hCt.eventually (eventually_mul_self_sqrtNearOne (A := N →L[ℝ] N))
    filter_upwards [hadj, hsq, hsymm] with w h1 h2 h3 x x'
    have hfix : adj S₀ (C w) = C w := eq_of_pairing S₀ fun y y' => by
      rw [adj_spec, hsymm₀ y (C w y'), hCapply w y', ← h3 y y', hCapply w y]
    have hR : adj S₀ (sqrtNearOne (N →L[ℝ] N) (C w)) = sqrtNearOne (N →L[ℝ] N) (C w) :=
      h1 hfix
    have hRR : sqrtNearOne (N →L[ℝ] N) (C w) (sqrtNearOne (N →L[ℝ] N) (C w) x') = C w x' :=
      congrArg (fun T : N →L[ℝ] N => T x') h2
    calc ⟪S₀ (sqrtNearOne (N →L[ℝ] N) (C w) x), sqrtNearOne (N →L[ℝ] N) (C w) x'⟫
        = ⟪S₀ (adj S₀ (sqrtNearOne (N →L[ℝ] N) (C w)) x),
            sqrtNearOne (N →L[ℝ] N) (C w) x'⟫ := by rw [hR]
      _ = ⟪S₀ x, sqrtNearOne (N →L[ℝ] N) (C w) (sqrtNearOne (N →L[ℝ] N) (C w) x')⟫ :=
        adj_spec S₀ _ _ _
      _ = ⟪S₀ x, C w x'⟫ := by rw [hRR]
      _ = ⟪x, S w x'⟫ := by rw [hsymm₀ x (C w x'), hCapply w x']
      _ = ⟪S w x, x'⟫ := (h3 x x').symm
  · intro J hJ
    set Φ : (N →L[ℝ] N) → (N →L[ℝ] N) := fun T =>
      (J.symm : N →L[ℝ] N).comp (T.comp (J : N →L[ℝ] N)) with hΦdef
    have hΦ1 : Φ 1 = 1 := ContinuousLinearMap.ext fun x => J.symm_apply_apply x
    have hΦc : ContinuousAt Φ 1 :=
      (continuous_const.clm_comp (continuous_id.clm_comp continuous_const)).continuousAt
    have hΦsq : ∀ a, Φ (a * a) = Φ a * Φ a := fun a => ContinuousLinearMap.ext fun x => by
      change J.symm (a (a (J x))) = J.symm (a (J (J.symm (a (J x)))))
      rw [J.apply_symm_apply]
    have hev := hCt.eventually (eventually_map_sqrtNearOne hΦ1 hΦc hΦsq)
    have hJ₀ : ∀ x, S₀ (J x) = J (S₀ x) := by
      intro x
      rw [hS₀x, hS₀x]
      exact hJ.self_of_nhds x
    filter_upwards [hev, hJ] with w h1 h2 x
    have hfix : Φ (C w) = C w := ContinuousLinearMap.ext fun y => by
      change J.symm (S₀.symm (S w (J y))) = S₀.symm (S w y)
      rw [h2 y]
      apply J.injective
      rw [J.apply_symm_apply]
      apply S₀.injective
      rw [S₀.apply_symm_apply, hJ₀, S₀.apply_symm_apply]
    have hR : Φ (sqrtNearOne (N →L[ℝ] N) (C w)) = sqrtNearOne (N →L[ℝ] N) (C w) := h1 hfix
    have h := congrArg (fun T : N →L[ℝ] N => J (T x)) hR
    have h' : J (J.symm (sqrtNearOne (N →L[ℝ] N) (C w) (J x))) =
        J (sqrtNearOne (N →L[ℝ] N) (C w) x) := h
    rwa [J.apply_symm_apply] at h'

end

end Finsler.Congruence
