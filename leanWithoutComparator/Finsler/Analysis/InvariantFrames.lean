module

public import Finsler.Analysis.InvariantNegative
public import Finsler.Analysis.FrameIndex

/-! Closed frames from an invariant negative subspace. Let β be a symmetric bilinear function
of negative index b on a finite dimensional real normed space, invariant under a linear map ρ
which also preserves a positive definite symmetric bilinear function and has no real
eigenvalue. A basis of a ρ-invariant negative definite subspace of dimension b is a negative
frame G with ρ G = G K for a matrix K without real eigenvalues. Hence, for a continuous family
of symmetric bilinear functions of index b with a symmetry T shifting the parameter by η, such
that T^{2r} preserves the function at the parameter 0 and a positive definite function and has
no real eigenvalue, there is a continuous family of negative frames over [0, 2 r η] with the
same frame at both ends. -/

@[expose] public section

namespace Finsler.InvariantFrames

open Module QuadraticForm QuadraticMap Set
open Finsler.DefiniteFrames Finsler.FramePath Finsler.FrameIndex Finsler.InvariantNegative

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {b : ℕ}

/-- **An invariant negative frame.** A symmetric bilinear function of negative index b which is
invariant under a linear map ρ preserving a positive definite symmetric bilinear function has a
negative frame G of b vectors with ρ G = G K; if ρ has no real eigenvalue, neither has K. -/
theorem exists_invariant_frame (β g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ρ : V →ₗ[ℝ] V)
    (hβ : ∀ v w, β v w = β w v) (hg : ∀ v w, g v w = g w v) (hpos : ∀ v, v ≠ 0 → 0 < g v v)
    (hβρ : ∀ v w, β (ρ v) (ρ w) = β v w) (hgρ : ∀ v w, g (ρ v) (ρ w) = g v w)
    (hb : sigNeg (LinearMap.BilinMap.toQuadraticMap β) = b)
    (heig : ∀ (μ : ℝ) (x : V), ρ x = μ • x → x = 0) :
    ∃ (G : Fin b → V) (K : Matrix (Fin b) (Fin b) ℝ), Neg β G ∧
      (fun i => ρ (G i)) = mulF G K ∧
      ∀ (μ : ℝ) (u : Fin b → ℝ), K.mulVec u = μ • u → u = 0 := by
  obtain ⟨W, hWinv, hWneg, hWdim⟩ :=
    exists_invariant_negative (finrank ℝ V) rfl β g ρ hβ hg hpos hβρ hgρ
  rw [hb] at hWdim
  have hcomb : ∀ u : Fin b → ℝ, comb (fun i => ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V)) u =
      ((∑ i, u i • (Module.finBasisOfFinrankEq ℝ W hWdim) i : W) : V) := by
    intro u
    simp only [comb, Submodule.coe_sum, Submodule.coe_smul]
  have hG : Neg β (fun i => ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V)) := by
    intro u hu
    rw [hcomb]
    have hne : (∑ i, u i • (Module.finBasisOfFinrankEq ℝ W hWdim) i : W) ≠ 0 := by
      intro h0
      apply hu
      funext i
      exact Fintype.linearIndependent_iff.mp
        (Module.finBasisOfFinrankEq ℝ W hWdim).linearIndependent u h0 i
    exact hWneg _ (Submodule.coe_mem _) fun h => hne (Subtype.ext h)
  have hmat : (fun i => ρ ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V)) =
      mulF (fun i => ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V))
        (LinearMap.toMatrix (Module.finBasisOfFinrankEq ℝ W hWdim)
          (Module.finBasisOfFinrankEq ℝ W hWdim) (ρ.restrict hWinv)) := by
    funext i
    have h1 : (ρ.restrict hWinv) ((Module.finBasisOfFinrankEq ℝ W hWdim) i) =
        ∑ j, (LinearMap.toMatrix (Module.finBasisOfFinrankEq ℝ W hWdim)
          (Module.finBasisOfFinrankEq ℝ W hWdim) (ρ.restrict hWinv)) j i •
            (Module.finBasisOfFinrankEq ℝ W hWdim) j := by
      conv_lhs => rw [← (Module.finBasisOfFinrankEq ℝ W hWdim).sum_repr
        ((ρ.restrict hWinv) ((Module.finBasisOfFinrankEq ℝ W hWdim) i))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.toMatrix_apply]
    have h2 := congrArg (Subtype.val) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2
  refine ⟨_, _, hG, hmat, fun μ u hu => ?_⟩
  have hlin := linearIndependent_of_neg hG
  have h3 : ρ (comb (fun i => ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V)) u) =
      μ • comb (fun i => ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V)) u := by
    have h4 : comb (fun i => ρ ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V)) u =
        ρ (comb (fun i => ((Module.finBasisOfFinrankEq ℝ W hWdim) i : V)) u) := by
      simp only [comb, map_sum, map_smul]
    rw [← h4, hmat, comb_mulF, hu, comb_smul]
  have h5 := heig μ _ h3
  funext i
  exact Fintype.linearIndependent_iff.mp hlin u h5 i

/-- **Closed frames from an invariant negative subspace.** For a family of index b with a
symmetry T shifting the parameter by η: if T^{2r} preserves the function at the parameter 0 and
a positive definite symmetric bilinear function and has no real eigenvalue, there is a
continuous family of negative frames over [0, 2 r η] with the same frame at both ends. -/
theorem exists_closed_frame_of_invariant {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hF : Family B b)
    (hb : sigNeg (LinearMap.BilinMap.toQuadraticMap (B 0)) = b) (T : V →L[ℝ] V) {η : ℝ}
    (hη : 0 < η) (hT : ∀ θ v w, B (θ + η) (T v) (T w) = B θ v w) {r : ℕ} (hr : 0 < r)
    (hinv : ∀ v w, B 0 ((T ^ (2 * r)) v) ((T ^ (2 * r)) w) = B 0 v w)
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hg : ∀ v w, g v w = g w v) (hpos : ∀ v, v ≠ 0 → 0 < g v v)
    (hgT : ∀ v w, g ((T ^ (2 * r)) v) ((T ^ (2 * r)) w) = g v w)
    (heig : ∀ (μ : ℝ) (x : V), (T ^ (2 * r)) x = μ • x → x = 0) :
    ∃ H : ℝ → Fin b → V, Continuous H ∧ H (((2 * r : ℕ) : ℝ) * η) = H 0 ∧
      ∀ θ ∈ Icc 0 (((2 * r : ℕ) : ℝ) * η), Neg (B θ) (H θ) := by
  obtain ⟨G₀, K, hG₀, hK, hK'⟩ := exists_invariant_frame (B 0) g (T ^ (2 * r)).toLinearMap
    (hF.symm 0) hg hpos hinv hgT hb heig
  exact exists_closed_frame T hF hη hT hG₀ hr hK hK'

end

end Finsler.InvariantFrames
