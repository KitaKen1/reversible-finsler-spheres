module

public import Finsler.Algebra.FramePath
public import Finsler.Analysis.OperatorIndex

/-! Negative frames and the negative index of inertia. For a symmetric bilinear function β on a
finite dimensional real normed space whose quadratic form has negative index of inertia b, there
is a negative frame of b vectors, and a vector which is β-orthogonal to a negative frame of b
vectors is not negative: otherwise the frame together with the vector would span a negative
definite subspace of dimension b + 1. The vectors of a negative frame are linearly independent.
Hence a continuous family of symmetric bilinear functions of constant negative index b is a
family of index b in the sense used for the construction of continuous frames; in particular
the forms ⟪A_θ v, w⟫ of a continuous family of symmetric operators of constant negative
index. -/

@[expose] public section

namespace Finsler.FrameIndex

open Module QuadraticForm QuadraticMap Finsler.DefiniteFrames Finsler.FramePath
open Finsler.OperatorIndex
open scoped RealInnerProductSpace

noncomputable section

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : ℕ}
  {β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

/-- The vectors of a negative frame are linearly independent. -/
theorem linearIndependent_of_neg {G : Fin b → V} (hG : Neg β G) : LinearIndependent ℝ G := by
  rw [Fintype.linearIndependent_iff]
  intro u hu
  by_contra hne
  have hu0 : u ≠ 0 := fun h => hne (fun i => by rw [h]; rfl)
  have h1 := hG u hu0
  have h2 : comb G u = 0 := hu
  rw [h2, map_zero] at h1
  simp at h1

/-- A negative frame extended by a negative vector orthogonal to it is a negative frame. -/
theorem neg_cons (hsym : ∀ v w, β v w = β w v) {G : Fin b → V} (hG : Neg β G) {w : V}
    (hw : ∀ i, β (G i) w = 0) (hneg : β w w < 0) :
    Neg β (Fin.cons w G : Fin (b + 1) → V) := by
  intro u hu
  have hcomb : comb (Fin.cons w G : Fin (b + 1) → V) u =
      u 0 • w + comb G (fun i => u i.succ) := by
    simp only [comb, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hc1 : β (comb G fun i => u i.succ) w = 0 := form_comb_left_eq_zero β G hw _
  have hc2 : β w (comb G fun i => u i.succ) = 0 := by
    rw [hsym]
    exact hc1
  have hval : β (comb (Fin.cons w G : Fin (b + 1) → V) u)
      (comb (Fin.cons w G : Fin (b + 1) → V) u) =
      u 0 ^ 2 * β w w + β (comb G fun i => u i.succ) (comb G fun i => u i.succ) := by
    rw [hcomb]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hc1,
      hc2]
    ring
  rw [hval]
  by_cases htail : (fun i : Fin b => u i.succ) = 0
  · have h0 : u 0 ≠ 0 := by
      intro h0
      apply hu
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun htail j
    have h1 : comb G (fun i : Fin b => u i.succ) = 0 := by
      rw [htail]
      simp [comb]
    rw [h1, map_zero, add_zero]
    exact mul_neg_of_pos_of_neg (by positivity) hneg
  · have h1 := hG _ htail
    have h2 : u 0 ^ 2 * β w w ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
    linarith

variable [FiniteDimensional ℝ V]

/-- A bilinear function whose quadratic form has negative index b has a negative frame of b
vectors. -/
theorem exists_neg_frame (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hb : sigNeg (LinearMap.BilinMap.toQuadraticMap β) = b) :
    ∃ G : Fin b → V, Neg β G := by
  obtain ⟨W, hW, hdef⟩ := exists_finrank_eq_sigNeg_and_negDef (LinearMap.BilinMap.toQuadraticMap β)
  rw [hb] at hW
  let B := Module.finBasisOfFinrankEq ℝ W hW
  refine ⟨fun i => (B i : V), fun u hu => ?_⟩
  have hx : comb (fun i => (B i : V)) u = ((∑ i, u i • B i : W) : V) := by
    simp only [comb, Submodule.coe_sum, Submodule.coe_smul]
  have hne : (∑ i, u i • B i : W) ≠ 0 := by
    intro h0
    apply hu
    funext i
    exact Fintype.linearIndependent_iff.mp B.linearIndependent u h0 i
  have h1 : 0 < -(β ((∑ i, u i • B i : W) : V) ((∑ i, u i • B i : W) : V)) := hdef _ hne
  rw [hx]
  linarith

/-- For a symmetric bilinear function of negative index b, a vector orthogonal to a negative
frame of b vectors is not negative. -/
theorem nonneg_of_orthogonal (hsym : ∀ v w, β v w = β w v)
    (hb : sigNeg (LinearMap.BilinMap.toQuadraticMap β) = b) {G : Fin b → V} (hG : Neg β G) {w : V}
    (hw : ∀ i, β (G i) w = 0) : 0 ≤ β w w := by
  by_contra hcon
  have hneg : β w w < 0 := not_le.mp hcon
  have hF := neg_cons hsym hG hw hneg
  have hli := linearIndependent_of_neg hF
  set W : Submodule ℝ V := Submodule.span ℝ (Set.range (Fin.cons w G : Fin (b + 1) → V))
    with hWdef
  have hrank : finrank ℝ W = b + 1 := by
    rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hdef : ((-(LinearMap.BilinMap.toQuadraticMap β)).restrict W).PosDef := by
    intro x hx
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp x.2
    have hu0 : u ≠ 0 := by
      intro h0
      apply hx
      apply Subtype.ext
      rw [← hu, h0]
      simp
    have h1 := hF u hu0
    have h2 : comb (Fin.cons w G : Fin (b + 1) → V) u = (x : V) := hu
    rw [h2] at h1
    change 0 < -(β (x : V) (x : V))
    linarith
  have hle := le_sigNeg_of_negDef (LinearMap.BilinMap.toQuadraticMap β) hdef
  rw [hrank, hb] at hle
  omega

/-- A continuous family of symmetric bilinear functions of constant negative index b is a
family of index b. -/
theorem family_of_sigNeg {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hcont : Continuous fun p : ℝ × V × V => B p.1 p.2.1 p.2.2)
    (hsymm : ∀ θ v w, B θ v w = B θ w v) (hb : ∀ θ, sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ)) = b) :
    Family B b where
  cont := hcont
  symm := hsymm
  ex := fun θ => exists_neg_frame (B θ) (hb θ)
  idx := fun θ _ hG _ hw => nonneg_of_orthogonal (hsymm θ) (hb θ) hG hw

end General

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {b : ℕ}

/-- A continuous family of symmetric operators of constant negative index b gives a family of
bilinear functions of index b. -/
theorem family_of_index {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    (hsymm : ∀ θ, (A θ).toLinearMap.IsSymmetric) (hb : ∀ θ, sigNeg (quad (A θ)) = b) :
    Family (fun θ => bilin (A θ)) b := by
  refine family_of_sigNeg ?_ (fun θ v w => (hsymm θ v w).trans (real_inner_comm _ _)) hb
  have h1 : Continuous fun p : ℝ × E × E => A p.1 p.2.1 :=
    (hA.comp continuous_fst).clm_apply (continuous_fst.comp continuous_snd)
  exact h1.inner (continuous_snd.comp continuous_snd)

end Operator

end

end Finsler.FrameIndex
