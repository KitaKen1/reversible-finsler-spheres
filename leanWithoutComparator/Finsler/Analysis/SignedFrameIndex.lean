module

public import Finsler.Geometry.FixedFrameCoordinates
public import Finsler.Analysis.InvolutionIndex

/-! Fixed signed-coordinate, energy, flow and index comparison. -/

@[expose] public section

namespace Finsler.SignedFrameIndex

open Module QuadraticMap QuadraticForm Finsler.FixedFrameCoordinates
open Finsler.RotationNatural Finsler.InvolutionIndex

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Index

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
theorem finrank_le_sigNeg_of_injective_neg (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (L : W →ₗ[ℝ] V) (hL : Function.Injective L)
    (hneg : ∀ w : W, w ≠ 0 → β (L w) (L w) < 0) :
    finrank ℝ W ≤ sigNeg (LinearMap.BilinMap.toQuadraticMap β) := by
  have hdef : ((-(LinearMap.BilinMap.toQuadraticMap β)).restrict (LinearMap.range L)).PosDef := by
    intro v hv
    obtain ⟨w, hw⟩ := v.2
    have hw0 : w ≠ 0 := by
      intro hz
      apply hv
      apply Subtype.ext
      rw [← hw, hz, map_zero]
      rfl
    change 0 < -(β (v : V) (v : V))
    rw [← hw]
    exact neg_pos.mpr (hneg w hw0)
  have h := le_sigNeg_of_negDef (LinearMap.BilinMap.toQuadraticMap β) hdef
  rw [← (LinearEquiv.ofInjective L hL).finrank_eq] at h
  exact h

variable {P : Type*} [AddCommGroup P] [Module ℝ P] [FiniteDimensional ℝ P]

theorem sigNeg_eq_of_split (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (E : (W × P) ≃ₗ[ℝ] V)
    (hneg : ∀ x : W, x ≠ 0 → β (E (x, 0)) (E (x, 0)) < 0)
    (hpos : ∀ y : P, y ≠ 0 → 0 < β (E (0, y)) (E (0, y))) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap β) = finrank ℝ W := by
  have hn := finrank_le_sigNeg_of_injective_neg β
    (E.toLinearMap.comp (LinearMap.inl ℝ W P))
    (E.injective.comp (fun x y h => congrArg Prod.fst h)) hneg
  have hp := finrank_le_sigNeg_of_injective_neg (-β)
    (E.toLinearMap.comp (LinearMap.inr ℝ W P))
    (E.injective.comp (fun x y h => congrArg Prod.snd h))
    (fun y hy => neg_neg_of_pos (hpos y hy))
  rw [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg] at hp
  have hd : finrank ℝ V = finrank ℝ W + finrank ℝ P := by
    rw [← E.finrank_eq, Module.finrank_prod]
  have hs := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := LinearMap.BilinMap.toQuadraticMap β)
  omega

end Index

section Signed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {b p : ℕ} (T : Module.End ℝ V)
  (E : ((Fin b → ℝ) × (Fin p → ℝ)) ≃ₗ[ℝ] V)
  (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
  (hcomm : ∀ ξ, T (E ξ) = E (coeffD d₁ d₂ ξ))

def fixedEquiv : (fixedCoeff d₁ × fixedCoeff d₂) ≃ₗ[ℝ] T.eigenspace 1 where
  toFun u := ⟨E (u.1.1, u.2.1), by
    rw [Module.End.mem_eigenspace_iff, one_smul, hcomm]
    apply E.injective.eq_iff.mpr
    exact Prod.ext u.1.2 u.2.2⟩
  invFun v :=
    let h : coeffD d₁ d₂ (E.symm (v : V)) = E.symm (v : V) := by
      apply E.injective
      rw [← hcomm, E.apply_symm_apply, Module.End.mem_eigenspace_iff.mp v.2, one_smul]
    (⟨(E.symm (v : V)).1, congrArg Prod.fst h⟩,
      ⟨(E.symm (v : V)).2, congrArg Prod.snd h⟩)
  left_inv u := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (E.symm_apply_apply (u.1.1, u.2.1))
    · apply Subtype.ext
      exact congrArg Prod.snd (E.symm_apply_apply (u.1.1, u.2.1))
  right_inv v := Subtype.ext (E.apply_symm_apply v)
  map_add' u v := by
    apply Subtype.ext
    change E ((u.1.1, u.2.1) + (v.1.1, v.2.1)) = E (u.1.1, u.2.1) + E (v.1.1, v.2.1)
    exact E.map_add _ _
  map_smul' c u := by
    apply Subtype.ext
    change E (c • (u.1.1, u.2.1)) = c • E (u.1.1, u.2.1)
    exact E.map_smul c _

include E hcomm in
omit [FiniteDimensional ℝ V] in
theorem finrank_fixed : finrank ℝ (T.eigenspace 1) =
    Fintype.card {i : Fin b // d₁ i = 1} + Fintype.card {i : Fin p // d₂ i = 1} := by
  rw [← (fixedEquiv T E d₁ d₂ hcomm).finrank_eq, Module.finrank_prod,
    finrank_fixedCoeff, finrank_fixedCoeff]

include hcomm in
theorem sigNeg_fixed (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hneg : ∀ x : Fin b → ℝ, x ≠ 0 → β (E (x, 0)) (E (x, 0)) < 0)
    (hpos : ∀ y : Fin p → ℝ, y ≠ 0 → 0 < β (E (0, y)) (E (0, y))) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T 1 β)) =
      Fintype.card {i : Fin b // d₁ i = 1} := by
  rw [← finrank_fixedCoeff d₁]
  apply sigNeg_eq_of_split (eigenForm T 1 β) (fixedEquiv T E d₁ d₂ hcomm)
  · intro x hx
    exact hneg x.1 (fun h => hx (Subtype.ext h))
  · intro y hy
    exact hpos y.1 (fun h => hy (Subtype.ext h))

end Signed

end

end Finsler.SignedFrameIndex
