module

public import Finsler.Geometry.FrameInverse

/-! The ambient split field near a circle of iterated polygons. Given a field V₀ on the root
polygons, the split field in frame coordinates is (V₀(z), J ξ), and the ambient split field at
an ambient polygon Q is the derivative of the frame coordinates at the coordinates of Q applied
to the split field there. Where the frame coordinates are invertible, the derivative of the
penalized energy at Q in the direction of the ambient split field is the derivative of the
penalized energy in frame coordinates in the direction of the split field; along the zero
section the base derivative is m² times the derivative of the penalized energy of the root
polygons with weight 1/m. Together with the split descent estimate:

  D pen(Q)(W(Q)) ≤ m² D pen_root(z)(V₀(z)) - c ‖ξ‖²

for Q with root polygon z in K₀, coefficients ξ with ‖ξ‖ ≤ R and ‖V₀(z)‖ ≤ κ. The ambient split
field is smooth where the frame coordinates are invertible and V₀ is smooth. -/

@[expose] public section

namespace Finsler.AmbientSplitField

open Module Filter Set
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)

/-- The ambient split field: the derivative of the frame coordinates applied to the split field
(V₀(z), J ξ) at the coordinates of the ambient polygon. -/
def splitW (Q : ZMod (m * N) → Ambient n) : ZMod (m * N) → Ambient n :=
  fderiv ℝ (coord m N G₁ G₂) (zOf m N Q, xiOf m N G₁ G₂ ψ Q)
    (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q))

/-- The derivative of the penalized energy in the direction of the ambient split field is the
derivative in frame coordinates in the direction of the split field. -/
theorem fderiv_pen_splitW (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (hpen : DifferentiableAt ℝ (pen F (m * N) 1) Q) :
    fderiv ℝ (pen F (m * N) 1) Q (splitW m N G₁ G₂ ψ V₀ Q) =
      fderiv ℝ (psi m N F G₁ G₂) (zOf m N Q, xiOf m N G₁ G₂ ψ Q)
        (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q)) := by
  have hc := coord_inverse m N G₁ G₂ ψ hQ
  have hcd : DifferentiableAt ℝ (coord m N G₁ G₂) (zOf m N Q, xiOf m N G₁ G₂ ψ Q) :=
    ((coord_contDiff m N G₁ G₂ hG₁ hG₂).differentiable (by simp)) _
  have hpen' : DifferentiableAt ℝ (pen F (m * N) 1)
      (coord m N G₁ G₂ (zOf m N Q, xiOf m N G₁ G₂ ψ Q)) := by
    rw [hc]
    exact hpen
  have h := (hpen'.hasFDerivAt.comp (zOf m N Q, xiOf m N G₁ G₂ ψ Q) hcd.hasFDerivAt).fderiv
  have e : psi m N F G₁ G₂ = pen F (m * N) 1 ∘ coord m N G₁ G₂ := rfl
  rw [e, h, hc]
  rfl

/-- The penalized energy along the zero section is m² times the penalized energy of the root
polygons with weight 1/m. -/
theorem psi_zero (z : ZMod N → Ambient n) :
    psi m N F G₁ G₂ (z, 0) = (m : ℝ) ^ 2 * pen F N (1 / m) z := by
  unfold psi
  rw [coord_zero]
  exact pen_iterate m N F 1 z

/-- The base derivative along the zero section is m² times the derivative of the penalized
energy of the root polygons. -/
theorem fderiv_psi_base {z : ZMod N → Ambient n}
    (hd : DifferentiableAt ℝ (psi m N F G₁ G₂) (z, 0)) (v : ZMod N → Ambient n) :
    fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) = (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) z v := by
  have hm : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne m))
  have hinl : HasFDerivAt (fun y : ZMod N → Ambient n => (y, (0 : (Fin b → ℝ) × (Fin p → ℝ))))
      (ContinuousLinearMap.inl ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ))) z :=
    (ContinuousLinearMap.inl ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ))).hasFDerivAt
  have hcomp := hd.hasFDerivAt.comp z hinl
  have e : (psi m N F G₁ G₂ ∘ fun y : ZMod N → Ambient n =>
      (y, (0 : (Fin b → ℝ) × (Fin p → ℝ)))) = fun y => (m : ℝ) ^ 2 * pen F N (1 / m) y := by
    funext y
    exact psi_zero m N F G₁ G₂ y
  rw [e] at hcomp
  have hroot : HasFDerivAt (pen F N (1 / m))
      (((m : ℝ) ^ 2)⁻¹ • (fderiv ℝ (psi m N F G₁ G₂) (z, 0)).comp
        (ContinuousLinearMap.inl ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ)))) z := by
    have h2 := hcomp.const_mul ((m : ℝ) ^ 2)⁻¹
    have e2 : (fun y => ((m : ℝ) ^ 2)⁻¹ * ((m : ℝ) ^ 2 * pen F N (1 / m) y)) = pen F N (1 / m) := by
      funext y
      rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
    rw [e2] at h2
    exact h2
  rw [hroot.fderiv]
  change fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) =
    (m : ℝ) ^ 2 * (((m : ℝ) ^ 2)⁻¹ * fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0))
  rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]

/-- **Descent of the ambient split field.** If R, κ, c are the constants of the split descent
estimate on K₀, then at an ambient polygon Q whose root polygon z lies in K₀, whose
coefficients ξ satisfy ‖ξ‖ ≤ R, at which the frame coordinates are invertible and the
penalized energy is differentiable, and with ‖V₀(z)‖ ≤ κ,

  D pen(Q)(W(Q)) ≤ m² D pen_root(z)(V₀(z)) - c ‖ξ‖². -/
theorem splitW_descent (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂) {K₀ : Set (ZMod N → Ambient n)}
    {R κ c : ℝ}
    (hest : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2)
    {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (hz : zOf m N Q ∈ K₀) (hξ : ‖xiOf m N G₁ G₂ ψ Q‖ ≤ R) (hv : ‖V₀ (zOf m N Q)‖ ≤ κ)
    (hR : 0 ≤ R) :
    fderiv ℝ (pen F (m * N) 1) Q (splitW m N G₁ G₂ ψ V₀ Q) ≤
      (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) (zOf m N Q) (V₀ (zOf m N Q)) -
        c * ‖xiOf m N G₁ G₂ ψ Q‖ ^ 2 := by
  obtain ⟨hC3, hd⟩ := hest (zOf m N Q) hz (xiOf m N G₁ G₂ ψ Q) hξ
  have hc := coord_inverse m N G₁ G₂ ψ hQ
  have hpen : DifferentiableAt ℝ (pen F (m * N) 1) Q := by
    rw [hc] at hC3
    exact hC3.differentiableAt (by norm_num)
  rw [fderiv_pen_splitW m N F G₁ G₂ ψ V₀ hG₁ hG₂ hQ hpen]
  have h0 : ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (zOf m N Q, 0)) :=
    (hest (zOf m N Q) hz 0 (by rw [norm_zero]; exact hR)).1
  have hd0 : DifferentiableAt ℝ (psi m N F G₁ G₂) (zOf m N Q, 0) := by
    have hcoord := coord_contDiff m N G₁ G₂ hG₁ hG₂
    exact (ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) (zOf m N Q, 0) h0
      (hcoord.contDiffAt.of_le (by simp))).differentiableAt (by norm_num)
  rw [← fderiv_psi_base m N F G₁ G₂ hd0]
  exact hd _ hv

/-- The ambient split field is smooth where the frame coordinates are invertible. -/
theorem splitW_contDiffAt (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (hV₀ : ContDiff ℝ ∞ V₀) {Q : ZMod (m * N) → Ambient n}
    (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))) :
    ContDiffAt ℝ ∞ (splitW m N G₁ G₂ ψ V₀) Q := by
  have hcoord := coord_contDiff m N G₁ G₂ hG₁ hG₂
  have hD : ContDiff ℝ ∞ (fderiv ℝ (coord m N G₁ G₂)) := hcoord.fderiv_right (by simp)
  have hz : ContDiffAt ℝ ∞ (zOf m N) Q := (zOf (n := n) m N).contDiff.contDiffAt
  have hξ := xiOf_contDiffAt m N G₁ G₂ ψ hG₁ hG₂ hQ
  have hpt : ContDiffAt ℝ ∞ (fun Q => (zOf m N Q, xiOf m N G₁ G₂ ψ Q)) Q := hz.prodMk hξ
  have hdir : ContDiffAt ℝ ∞ (fun Q => (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q))) Q :=
    (hV₀.contDiffAt.comp Q hz).prodMk ((swapJ (b := b) (p := p)).contDiff.contDiffAt.comp Q hξ)
  exact (hD.contDiffAt.comp Q hpt).clm_apply hdir

/-! ### Small pseudo-gradients -/

/-- A smooth compactly supported pseudo-gradient whose values are bounded by a prescribed
constant: a positive multiple of a pseudo-gradient. -/
theorem exists_small_pseudoGradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) {A : Set E}
    (hA : IsCompact A) (hAO : A ⊆ O) (hne : ∀ x ∈ A, fderiv ℝ f x ≠ 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ O ∧
      (∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) ∧ (∀ y ∈ A, fderiv ℝ f y (V y) < 0) ∧
      ∀ y, ‖V y‖ ≤ κ := by
  obtain ⟨V, hV, hVc, hVs, hle, hlt⟩ := PseudoGradient.exists_pseudoGradient hO hf hA hAO hne
  obtain ⟨M, hM⟩ := hV.continuous.bounded_above_of_compact_support hVc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hc : 0 < κ / (M + 1) := div_pos hκ (by linarith)
  refine ⟨fun y => (κ / (M + 1)) • V y, contDiff_const.smul hV, hVc.smul_left (f := fun _ => κ / (M + 1)),
    (tsupport_smul_subset_right (fun _ => κ / (M + 1)) V).trans hVs, fun y hy => ?_,
    fun y hy => ?_, fun y => ?_⟩
  · rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (hle y hy)
  · rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc (hlt y hy)
  · rw [norm_smul, Real.norm_of_nonneg hc.le]
    have h1 := hM y
    calc κ / (M + 1) * ‖V y‖ ≤ κ / (M + 1) * M := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ κ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-! ### The flow in frame coordinates -/

/-- The product curve in frame coordinates: the flow of V₀ on the root polygons, and the linear
hyperbolic flow (e^t x, e^{-t} y) on the coefficients. -/
def prodCurve {K₀ : NNReal} (hV₀ : LipschitzWith K₀ V₀) (z : ZMod N → Ambient n)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) (t : ℝ) :
    (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) :=
  (ODE.globalSolution V₀ hV₀ z t, (Real.exp t • ξ.1, Real.exp (-t) • ξ.2))

omit [NeZero m] in
theorem prodCurve_zero {K₀ : NNReal} (hV₀ : LipschitzWith K₀ V₀) (z : ZMod N → Ambient n)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : prodCurve N V₀ hV₀ z ξ 0 = (z, ξ) := by
  unfold prodCurve
  rw [ODE.globalSolution_zero, neg_zero, Real.exp_zero, one_smul, one_smul]

omit [NeZero m] in
/-- The product curve solves the split field equation in frame coordinates. -/
theorem hasDerivAt_prodCurve {K₀ : NNReal} (hV₀ : LipschitzWith K₀ V₀) (z : ZMod N → Ambient n)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) (t : ℝ) :
    HasDerivAt (prodCurve N V₀ hV₀ z ξ)
      (V₀ (prodCurve N V₀ hV₀ z ξ t).1, swapJ (prodCurve N V₀ hV₀ z ξ t).2) t := by
  have h1 := ODE.hasDerivAt_globalSolution V₀ hV₀ z t
  have h2 : HasDerivAt (fun s => Real.exp s • ξ.1) (Real.exp t • ξ.1) t :=
    (Real.hasDerivAt_exp t).smul_const ξ.1
  have h3 : HasDerivAt (fun s => Real.exp (-s) • ξ.2) (-(Real.exp (-t) • ξ.2)) t := by
    have h4 : HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
      have h5 := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
      rw [mul_neg_one] at h5
      exact h5
    have h6 := h4.smul_const ξ.2
    rw [neg_smul] at h6
    exact h6
  exact h1.prodMk (h2.prodMk h3)

/-- The image of the product curve under the frame coordinates is an integral curve of the
ambient split field where the frame coordinates are invertible. -/
theorem hasDerivAt_coord_prodCurve (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K₀ : NNReal} (hV₀ : LipschitzWith K₀ V₀) (z : ZMod N → Ambient n)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) {t : ℝ}
    (hunit : IsUnit (matA m N G₁ G₂ ψ (prodCurve N V₀ hV₀ z ξ t).1)) :
    HasDerivAt (fun s => coord m N G₁ G₂ (prodCurve N V₀ hV₀ z ξ s))
      (splitW m N G₁ G₂ ψ V₀ (coord m N G₁ G₂ (prodCurve N V₀ hV₀ z ξ t))) t := by
  have hcd : HasFDerivAt (coord m N G₁ G₂)
      (fderiv ℝ (coord m N G₁ G₂) (prodCurve N V₀ hV₀ z ξ t)) (prodCurve N V₀ hV₀ z ξ t) :=
    ((coord_contDiff m N G₁ G₂ hG₁ hG₂).differentiable (by simp) _).hasFDerivAt
  have h := hcd.comp_hasDerivAt t (hasDerivAt_prodCurve N V₀ hV₀ z ξ t)
  obtain ⟨hz, hξ⟩ := inverse_coord m N G₁ G₂ ψ hunit (prodCurve N V₀ hV₀ z ξ t).2
  rw [Prod.mk.eta] at hz hξ
  unfold splitW
  rw [hz, hξ]
  exact h

/-- **The flow near the critical circle is the product flow in frame coordinates.** If a
globally Lipschitz field V agrees with the ambient split field on a set U, and the image of the
product curve stays in U with invertible frame coordinates on [0, T], then the flow of V from
the frame coordinates of (z, ξ) is the image of the product curve on [0, T]. -/
theorem globalSolution_eq_coord (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : NNReal}
    (hV : LipschitzWith K V) {U : Set (ZMod (m * N) → Ambient n)}
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {K₀ : NNReal} (hV₀ : LipschitzWith K₀ V₀)
    (z : ZMod N → Ambient n) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) {T : ℝ}
    (hin : ∀ t ∈ Icc 0 T, coord m N G₁ G₂ (prodCurve N V₀ hV₀ z ξ t) ∈ U ∧
      IsUnit (matA m N G₁ G₂ ψ (prodCurve N V₀ hV₀ z ξ t).1)) :
    ∀ t ∈ Icc 0 T, ODE.globalSolution V hV (coord m N G₁ G₂ (z, ξ)) t =
      coord m N G₁ G₂ (prodCurve N V₀ hV₀ z ξ t) := by
  intro t ht
  have hg : ∀ s ∈ Icc 0 T, HasDerivAt (fun r => coord m N G₁ G₂ (prodCurve N V₀ hV₀ z ξ r))
      (V (coord m N G₁ G₂ (prodCurve N V₀ hV₀ z ξ s))) s := by
    intro s hs
    rw [hU _ (hin s hs).1]
    exact hasDerivAt_coord_prodCurve m N G₁ G₂ ψ V₀ hG₁ hG₂ hV₀ z ξ (hin s hs).2
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ y => V y) (s := fun _ => univ)
    (K := K) (fun _ _ => hV.lipschitzOnWith)
    ((ODE.continuous_globalSolution_apply V hV _).continuousOn)
    (fun s _ => (ODE.hasDerivAt_globalSolution V hV _ s).hasDerivWithinAt)
    (fun _ _ => trivial)
    (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun _ _ => trivial)
    (by rw [ODE.globalSolution_zero, prodCurve_zero])
  exact heq ht

end

end Finsler.AmbientSplitField
