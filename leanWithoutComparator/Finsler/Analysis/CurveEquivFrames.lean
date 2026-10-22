module

public import Finsler.Analysis.EquivariantApprox

/-! Continuous parameterized frames descend to compact curve images when equal curve points
have equal frames. Equivariant negative frames then extend smoothly to invariant neighborhoods. -/

@[expose] public section

namespace Finsler.CurveEquivFrames

open Set Topology
open Finsler.DefiniteFrames Finsler.EquivariantApprox
open scoped ContDiff

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {b : ℕ}

/-- The induced signed symmetry on a frame, as a continuous linear map. -/
def signAction (T : V →L[ℝ] V) (d : Fin b → ℝ) :
    (Fin b → V) →L[ℝ] (Fin b → V) :=
  ContinuousLinearMap.pi fun i => d i • T.comp (ContinuousLinearMap.proj i)

theorem signAction_apply (T : V →L[ℝ] V) (d : Fin b → ℝ) (G : Fin b → V) (i : Fin b) :
    signAction T d G i = d i • T (G i) := rfl

theorem signAction_involutive (T : V →L[ℝ] V) (hTT : ∀ v, T (T v) = v)
    (d : Fin b → ℝ) (hd : ∀ i, d i * d i = 1) (G : Fin b → V) :
    signAction T d (signAction T d G) = G := by
  funext i
  simp only [signAction_apply, map_smul, smul_smul, hd, one_smul, hTT]

theorem signAction_eq_mulF (T : V →L[ℝ] V) (d : Fin b → ℝ) (G : Fin b → V) :
    signAction T d G = mulF (fun i => T (G i)) (Matrix.diagonal d) := by
  funext i
  simp [signAction_apply, mulF, Matrix.diagonal_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The half-period law supplies explicit witnesses on a full period: use θ+ℓ on the first
half and θ-ℓ on the second half. -/
theorem half_shift_witnesses (τ : E → E) (S : (Fin b → V) → Fin b → V)
    (hτ : ∀ x, τ (τ x) = x) (hS : ∀ v, S (S v) = v)
    {c : ℝ → E} {H : ℝ → Fin b → V} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hc : ∀ θ ∈ Icc 0 ℓ, c (θ + ℓ) = τ (c θ))
    (hH : ∀ θ ∈ Icc 0 ℓ, H (θ + ℓ) = S (H θ)) :
    ∀ θ ∈ Icc 0 (2 * ℓ), ∃ θ' ∈ Icc 0 (2 * ℓ), c θ' = τ (c θ) ∧ H θ' = S (H θ) := by
  intro θ hθ
  by_cases hle : θ ≤ ℓ
  · exact ⟨θ + ℓ, ⟨by linarith [hθ.1], by linarith⟩,
      hc θ ⟨hθ.1, hle⟩, hH θ ⟨hθ.1, hle⟩⟩
  · have ht : θ - ℓ ∈ Icc (0 : ℝ) ℓ := ⟨by linarith, by linarith [hθ.2]⟩
    have hc' := congrArg τ (hc (θ - ℓ) ht)
    have hH' := congrArg S (hH (θ - ℓ) ht)
    rw [sub_add_cancel, hτ] at hc'
    rw [sub_add_cancel, hS] at hH'
    exact ⟨θ - ℓ, ⟨ht.1, by linarith [ht.2]⟩, hc'.symm, hH'.symm⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
/-- A continuous parameterized frame descends to the compact curve image when its value
depends only on the point of the curve. -/
theorem continuous_frame_on_image {c : ℝ → E} (hc : Continuous c) {L : ℝ}
    {H : ℝ → Fin b → V} (hH : Continuous H)
    (hsame : ∀ θ ∈ Icc 0 L, ∀ θ' ∈ Icc 0 L, c θ = c θ' → H θ = H θ') :
    ∃ f : C(c '' Icc 0 L, Fin b → V),
      ∀ θ (hθ : θ ∈ Icc 0 L), f ⟨c θ, ⟨θ, hθ, rfl⟩⟩ = H θ := by
  let K : Set E := c '' Icc 0 L
  let π : Icc (0 : ℝ) L → K := fun θ => ⟨c θ, ⟨θ, θ.2, rfl⟩⟩
  have hπc : Continuous π := (hc.comp continuous_subtype_val).subtype_mk _
  have hπs : Function.Surjective π := by
    intro z
    obtain ⟨θ, hθ, he⟩ := z.2
    exact ⟨⟨θ, hθ⟩, Subtype.ext he⟩
  have hπ : IsQuotientMap π := hπc.isClosedMap.isQuotientMap hπc hπs
  let f : K → Fin b → V := fun z => H (Classical.choose z.2)
  have he : ∀ θ : Icc (0 : ℝ) L, f (π θ) = H θ := by
    intro θ
    have hs := Classical.choose_spec (π θ).2
    exact hsame _ hs.1 _ θ.2 hs.2
  have hf : Continuous f := hπ.continuous_iff.mpr (by
    have h : Continuous (fun θ : Icc (0 : ℝ) L => H (θ : ℝ)) := hH.comp continuous_subtype_val
    convert h using 1
    exact funext he)
  exact ⟨⟨f, hf⟩, fun θ hθ => he ⟨θ, hθ⟩⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]

/-- A parameterized equivariant negative frame yields an equivariant smooth frame field on
an invariant neighbourhood of the entire compact curve image. -/
theorem exists_equivariant_field_on_curve (τ : E →L[ℝ] E)
    (S : (Fin b → V) →L[ℝ] (Fin b → V)) (hτ : ∀ x, τ (τ x) = x)
    (hS : ∀ v, S (S v) = v) {c : ℝ → E} (hc : Continuous c) {L : ℝ}
    {H : ℝ → Fin b → V} (hH : Continuous H)
    (hsame : ∀ θ ∈ Icc 0 L, ∀ θ' ∈ Icc 0 L, c θ = c θ' → H θ = H θ')
    (hshift : ∀ θ ∈ Icc 0 L, ∃ θ' ∈ Icc 0 L, c θ' = τ (c θ) ∧ H θ' = S (H θ))
    {O : Set E} (hO : IsOpen O) (hcO : ∀ θ ∈ Icc 0 L, c θ ∈ O)
    (Q : E → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ContinuousOn (fun p : E × V × V => Q p.1 p.2.1 p.2.2) (O ×ˢ univ))
    (hneg : ∀ θ ∈ Icc 0 L, Neg (Q (c θ)) (H θ)) :
    ∃ (G : E → Fin b → V) (U : Set E), ContDiff ℝ ∞ G ∧
      (∀ x, G (τ x) = S (G x)) ∧ IsOpen U ∧
      (∀ θ ∈ Icc 0 L, c θ ∈ U) ∧ U ⊆ O ∧
      (∀ x, τ x ∈ U ↔ x ∈ U) ∧ ∀ x ∈ U, Neg (Q x) (G x) := by
  obtain ⟨f, hf⟩ := continuous_frame_on_image hc hH hsame
  have hK : IsCompact (c '' Icc (0 : ℝ) L) := isCompact_Icc.image hc
  have hKO : c '' Icc 0 L ⊆ O := by rintro _ ⟨θ, hθ, rfl⟩; exact hcO θ hθ
  have hKτ : ∀ x ∈ c '' Icc 0 L, τ x ∈ c '' Icc 0 L := by
    rintro _ ⟨θ, hθ, rfl⟩
    obtain ⟨θ', hθ', he, -⟩ := hshift θ hθ
    exact ⟨θ', hθ', he⟩
  have hfeq : ∀ x : c '' Icc 0 L, f ⟨τ x, hKτ x x.2⟩ = S (f x) := by
    intro x
    obtain ⟨θ, hθ, he⟩ := x.2
    have hx : x = ⟨c θ, ⟨θ, hθ, rfl⟩⟩ := Subtype.ext he.symm
    subst x
    obtain ⟨θ', hθ', he', hH'⟩ := hshift θ hθ
    have hpoint : (⟨τ (c θ), hKτ (c θ) ⟨θ, hθ, rfl⟩⟩ : c '' Icc 0 L) =
        ⟨c θ', ⟨θ', hθ', rfl⟩⟩ := Subtype.ext he'.symm
    rw [hpoint, hf θ' hθ', hf θ hθ]
    exact hH'
  have hfneg : ∀ x : c '' Icc 0 L, Neg (Q x) (f x) := by
    intro x
    obtain ⟨θ, hθ, he⟩ := x.2
    have hx : x = ⟨c θ, ⟨θ, hθ, rfl⟩⟩ := Subtype.ext he.symm
    rw [hx, hf θ hθ]
    exact hneg θ hθ
  obtain ⟨G, U, hG, hGeq, hU, hKU, hUO, hUτ, hGU⟩ :=
    exists_equivariant_negative_extension τ S hτ hS hK hO hKO hKτ Q hQ f hfeq hfneg
  exact ⟨G, U, hG, hGeq, hU, fun θ hθ => hKU ⟨θ, hθ, rfl⟩, hUO, hUτ, hGU⟩

end

end Finsler.CurveEquivFrames
