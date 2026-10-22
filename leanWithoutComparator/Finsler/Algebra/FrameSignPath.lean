module

public import Finsler.Algebra.FramePath

/-! Endpoints of paths of negative frames, with orientation absorbed by diagonal signs.
The existing frame path ends at the requested frame times an arbitrary invertible matrix.
Connect that matrix to a diagonal sign matrix and correct the path explicitly. No orientability
or real-eigenvalue hypothesis is needed for this signed endpoint statement. -/

@[expose] public section

namespace Finsler.FrameSignPath

open Matrix Set Topology Finsler.DefiniteFrames Finsler.MatrixPath Finsler.FramePath

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : ℕ}
  {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

/-- A path of negative frames can end at any prescribed negative frame up to diagonal signs.
This is the half-period endpoint condition needed for a twisted adapted frame. -/
theorem exists_path_sign_endpoint (hF : Family B b) {G₀ G₁ : Fin b → V}
    (hG₀ : Neg (B 0) G₀) {ℓ : ℝ} (hℓ : 0 < ℓ) (hG₁ : Neg (B ℓ) G₁) :
    ∃ d : Fin b → ℝ, (∀ i, d i * d i = 1) ∧
      ∃ H : ℝ → Fin b → V, Continuous H ∧ H 0 = G₀ ∧
        H ℓ = mulF G₁ (Matrix.diagonal d) ∧ ∀ θ ∈ Icc 0 ℓ, Neg (B θ) (H θ) := by
  obtain ⟨H, hH, hH0, hneg, K, hK, hend⟩ := exists_path_to hF hG₀ hℓ hG₁
  obtain ⟨d, γ, hγ, hγ0, hγ1, hγdet⟩ := exists_conn_sign hK
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.mpr hK
  have hKinv : K⁻¹.det ≠ 0 := by
    intro h
    have e : (K⁻¹ * K).det = 1 := by rw [Matrix.nonsing_inv_mul K hKu, Matrix.det_one]
    rw [Matrix.det_mul, h, zero_mul] at e
    exact zero_ne_one e
  have hC : Continuous fun θ : ℝ => K⁻¹ * γ (θ / ℓ) :=
    continuous_const.matrix_mul (hγ.comp (continuous_id.div_const ℓ))
  refine ⟨fun i => sgn (d i), fun i => sgn_mul_sgn _,
    fun θ => mulF (H θ) (K⁻¹ * γ (θ / ℓ)),
    mulF_continuous.comp (hH.prodMk hC), ?_, ?_, ?_⟩
  · change mulF (H 0) (K⁻¹ * γ (0 / ℓ)) = G₀
    rw [zero_div, hγ0, Matrix.nonsing_inv_mul K hKu, mulF_one, hH0]
  · change mulF (H ℓ) (K⁻¹ * γ (ℓ / ℓ)) = _
    rw [div_self hℓ.ne', hγ1, hend, mulF_mul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv K hKu, Matrix.one_mul]
  · intro θ hθ
    apply neg_mulF (hneg θ hθ)
    rw [Matrix.det_mul]
    exact mul_ne_zero hKinv (hγdet _)

/-- With a half-period symmetry of the forms, the signed endpoint is the transformed initial
frame. Closing the doubled path and descending it to the actual critical circle are separate. -/
theorem exists_half_frame (hF : Family B b) (T : V →L[ℝ] V) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hT : ∀ v w, B ℓ (T v) (T w) = B 0 v w)
    {G₀ : Fin b → V} (hG₀ : Neg (B 0) G₀) :
    ∃ d : Fin b → ℝ, (∀ i, d i * d i = 1) ∧
      ∃ H : ℝ → Fin b → V, Continuous H ∧ H 0 = G₀ ∧
        H ℓ = mulF (fun i => T (G₀ i)) (Matrix.diagonal d) ∧
        ∀ θ ∈ Icc 0 ℓ, Neg (B θ) (H θ) := by
  apply exists_path_sign_endpoint hF hG₀ hℓ
  intro u hu
  rw [FramePath.comb_map T, hT]
  exact hG₀ u hu

/-- **Twisted closed frames.** An involutive half-period symmetry gives a closed continuous
negative frame over a full period, with a fixed diagonal sign action on the half-period.
The orientation of half-period transport is absorbed in these signs. -/
theorem exists_twisted_closed_frame (hF : Family B b) (T : V →L[ℝ] V)
    (hTT : ∀ v, T (T v) = v) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hT : ∀ θ v w, B (θ + ℓ) (T v) (T w) = B θ v w)
    {G₀ : Fin b → V} (hG₀ : Neg (B 0) G₀) :
    ∃ d : Fin b → ℝ, (∀ i, d i * d i = 1) ∧
      ∃ C : ℝ → Fin b → V, Continuous C ∧ C 0 = G₀ ∧ C (2 * ℓ) = G₀ ∧
        (∀ θ ∈ Icc 0 (2 * ℓ), Neg (B θ) (C θ)) ∧
        ∀ θ ∈ Icc 0 ℓ, C (θ + ℓ) = mulF (fun i => T (C θ i)) (Matrix.diagonal d) := by
  have hT0 : ∀ v w, B ℓ (T v) (T w) = B 0 v w := by simpa using hT 0
  obtain ⟨d, hd, H, hH, hH0, hend, hneg⟩ := exists_half_frame hF T hℓ hT0 hG₀
  have hDD : Matrix.diagonal d * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have he : (fun i => d i * d i) = fun _ => (1 : ℝ) := funext hd
    rw [he, Matrix.diagonal_one]
  have hDdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ hi => by
      have h := hd i
      rw [hi, zero_mul] at h
      exact zero_ne_one h
  let P : ℝ → Fin b → V := fun θ => mulF (fun i => T (H θ i)) (Matrix.diagonal d)
  have hP : Continuous P := mulF_continuous.comp
    ((continuous_pi fun i => T.continuous.comp ((continuous_apply i).comp hH)).prodMk continuous_const)
  have hjoin : H ℓ = P 0 := by change H ℓ = mulF (fun i => T (H 0 i)) _; rw [hH0, hend]
  let C : ℝ → Fin b → V := fun θ => H (min θ ℓ) + P (max θ ℓ - ℓ) - P 0
  have hCl : ∀ θ, θ ≤ ℓ → C θ = H θ := by
    intro θ hθ
    simp only [C, min_eq_left hθ, max_eq_right hθ, sub_self, add_sub_cancel_right]
  have hCr : ∀ θ, ℓ ≤ θ → C θ = P (θ - ℓ) := by
    intro θ hθ
    simp only [C, min_eq_right hθ, max_eq_left hθ]
    rw [hjoin, add_sub_cancel_left]
  refine ⟨d, hd, C, ((hH.comp (continuous_id.min continuous_const)).add
    (hP.comp ((continuous_id.max continuous_const).sub continuous_const))).sub continuous_const,
    (hCl 0 hℓ.le).trans hH0, ?_, ?_, ?_⟩
  · rw [hCr _ (by linarith), show 2 * ℓ - ℓ = ℓ by ring]
    change mulF (fun i => T (H ℓ i)) (Matrix.diagonal d) = G₀
    rw [hend, FramePath.map_mulF_clm T, mulF_mul, hDD, mulF_one]
    exact funext fun i => hTT (G₀ i)
  · intro θ hθ
    rcases le_total θ ℓ with hle | hge
    · rw [hCl θ hle]
      exact hneg θ ⟨hθ.1, hle⟩
    · rw [hCr θ hge]
      have hs : θ - ℓ ∈ Icc (0 : ℝ) ℓ := ⟨by linarith [hge], by linarith [hθ.2]⟩
      have h := FramePath.neg_map T hT (hneg _ hs)
      rw [sub_add_cancel] at h
      exact neg_mulF h hDdet
  · intro θ hθ
    rw [hCr _ (by linarith [hθ.1]), hCl θ hθ.2, add_sub_cancel_right]

end

end Finsler.FrameSignPath
