module

public import Finsler.Algebra.SymmetricBlocks
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! Invariant maximal negative definite subspaces. Let β and g be symmetric bilinear functions
on a finite dimensional real normed space, g positive definite, and ρ a linear map preserving
both. Then there is a ρ-invariant subspace on which β is negative definite and whose dimension
is the negative index of inertia of β.

If β is negative somewhere, the quotient β(v, v) / g(v, v) has a minimum λ < 0 on the unit
sphere, attained at v₁; then β - λ g is nonnegative and vanishes at v₁, so v₁ lies in the kernel
W₁ of β - λ g. This kernel is ρ-invariant and β = λ g is negative definite on it. Its
g-orthogonal complement U is ρ-invariant, complementary to W₁ and β-orthogonal to W₁, so the
negative index of β is the sum of the negative indices on W₁ and on U; the statement follows by
induction on the dimension, applied to U. No spectral theory is used. -/

@[expose] public section

namespace Finsler.InvariantNegative

open Module QuadraticForm QuadraticMap

noncomputable section

/-- A real quadratic polynomial without constant term which is nonnegative everywhere has no
linear term. -/
theorem eq_zero_of_quadratic_nonneg {a b : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) :
    a = 0 := by
  by_contra ha
  have hs : 0 < |b| + 1 := by positivity
  have h1 := h (-a / (|b| + 1))
  have ha2 : 0 < a ^ 2 := by positivity
  have hq : b ≤ |b| := le_abs_self _
  have e : 2 * (-a / (|b| + 1)) * a + (-a / (|b| + 1)) ^ 2 * b =
      a ^ 2 * (b - 2 * (|b| + 1)) / (|b| + 1) ^ 2 := by
    field_simp
    ring
  rw [e] at h1
  have hneg : a ^ 2 * (b - 2 * (|b| + 1)) / (|b| + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith [abs_nonneg b]
    · positivity
  linarith

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A vector at which a nonnegative symmetric bilinear function vanishes is in its kernel. -/
theorem form_eq_zero_of_nonneg {γ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hsym : ∀ v w, γ v w = γ w v)
    (hnn : ∀ v, 0 ≤ γ v v) {v : V} (hv : γ v v = 0) (w : V) : γ v w = 0 := by
  refine eq_zero_of_quadratic_nonneg (b := γ w w) fun t => ?_
  have h := hnn (v + t • w)
  have e : γ (v + t • w) (v + t • w) = 2 * t * γ v w + t ^ 2 * γ w w := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv,
      hsym w v]
    ring
  rw [e] at h
  exact h

end Algebra

section Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The quadratic function of a bilinear function on a finite dimensional space is
continuous. -/
theorem continuous_quad (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Continuous fun v : V => β v v := by
  have h1 : Continuous fun v : V =>
      (LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ β)) v v :=
    (ContinuousLinearMap.continuous _).clm_apply continuous_id
  exact h1

/-- If β is negative somewhere, the quotient of β by a positive definite g has a negative
minimum, attained at a nonzero vector. -/
theorem exists_min_ratio (β g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < g v v) {v₀ : V}
    (hv₀ : β v₀ v₀ < 0) :
    ∃ (lam : ℝ) (v₁ : V), lam < 0 ∧ v₁ ≠ 0 ∧ β v₁ v₁ = lam * g v₁ v₁ ∧
      ∀ v, lam * g v v ≤ β v v := by
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv₀
    exact lt_irrefl _ hv₀
  have hscale : ∀ (γ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (c : ℝ) (v : V), γ (c • v) (c • v) = c ^ 2 * γ v v := by
    intro γ c v
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hsph : ∀ v : V, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
    intro v hv
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hne0 : ∀ v ∈ Metric.sphere (0 : V) 1, v ≠ 0 := by
    intro v hv h0
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hv
    exact zero_ne_one hv
  have hcont : ContinuousOn (fun v : V => β v v / g v v) (Metric.sphere (0 : V) 1) :=
    (continuous_quad β).continuousOn.div (continuous_quad g).continuousOn
      fun v hv => (hpos v (hne0 v hv)).ne'
  obtain ⟨v₁, hv₁, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
    ⟨_, hsph v₀ hv₀0⟩ hcont
  have hv₁0 := hne0 v₁ hv₁
  have hg₁ := hpos v₁ hv₁0
  have hratio : ∀ v : V, v ≠ 0 → β v₁ v₁ / g v₁ v₁ ≤ β v v / g v v := by
    intro v hv
    have h := hmin (hsph v hv)
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    change β v₁ v₁ / g v₁ v₁ ≤ β (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) / g (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at h
    rw [hscale β, hscale g, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hn))] at h
    exact h
  refine ⟨β v₁ v₁ / g v₁ v₁, v₁, ?_, hv₁0, ?_, fun v => ?_⟩
  · exact lt_of_le_of_lt (hratio v₀ hv₀0) (div_neg_of_neg_of_pos hv₀ (hpos v₀ hv₀0))
  · rw [div_mul_cancel₀ _ hg₁.ne']
  · by_cases hv : v = 0
    · rw [hv, map_zero, map_zero, mul_zero]
    · have h := hratio v hv
      rwa [le_div_iff₀ (hpos v hv)] at h

end Analysis

/-- **Invariant maximal negative definite subspaces.** For symmetric bilinear functions β and g
on a finite dimensional real normed space, g positive definite, and a linear map ρ preserving
both, there is a ρ-invariant subspace on which β is negative definite and whose dimension is
the negative index of inertia of β. -/
theorem exists_invariant_negative : ∀ (d : ℕ) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V], finrank ℝ V = d →
    ∀ (β g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ρ : V →ₗ[ℝ] V), (∀ v w, β v w = β w v) →
      (∀ v w, g v w = g w v) → (∀ v, v ≠ 0 → 0 < g v v) →
      (∀ v w, β (ρ v) (ρ w) = β v w) → (∀ v w, g (ρ v) (ρ w) = g v w) →
      ∃ W : Submodule ℝ V, (∀ v ∈ W, ρ v ∈ W) ∧ (∀ v ∈ W, v ≠ 0 → β v v < 0) ∧
        finrank ℝ W = sigNeg (LinearMap.BilinMap.toQuadraticMap β) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro V _ _ _ hd β g ρ hβ hg hpos hβρ hgρ
    by_cases hnn : ∀ v, 0 ≤ β v v
    · -- no negative vector: the zero subspace
      refine ⟨⊥, fun v hv => by rw [(Submodule.mem_bot ℝ).mp hv, map_zero]; exact Submodule.zero_mem _,
        fun v hv hv0 => absurd ((Submodule.mem_bot ℝ).mp hv) hv0, ?_⟩
      rw [finrank_bot]
      exact ((QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero
        (LinearMap.BilinMap.toQuadraticMap β)).mp hnn).symm
    · obtain ⟨v₀, hv₀⟩ := not_forall.mp hnn
      have hv₀' : β v₀ v₀ < 0 := not_le.mp hv₀
      obtain ⟨lam, v₁, hlam, hv₁0, hv₁, hmin⟩ := exists_min_ratio β g hpos hv₀'
      -- ρ is bijective
      have hρinj : Function.Injective ρ := by
        rw [injective_iff_map_eq_zero]
        intro v hv
        by_contra hv0
        have h := hpos v hv0
        rw [← hgρ v v, hv, map_zero] at h
        exact lt_irrefl _ h
      -- the kernel of β - λ g
      set W₁ : Submodule ℝ V := LinearMap.ker (β - lam • g) with hW₁
      have hmemW₁ : ∀ v, v ∈ W₁ ↔ ∀ w, β v w = lam * g v w := by
        intro v
        rw [hW₁, LinearMap.mem_ker]
        constructor
        · intro h w
          have h' := LinearMap.congr_fun h w
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
            LinearMap.zero_apply] at h'
          linarith
        · intro h
          refine LinearMap.ext fun w => ?_
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
            LinearMap.zero_apply]
          linarith [h w]
      have hv₁W : v₁ ∈ W₁ := by
        rw [hmemW₁]
        intro w
        have hγsym : ∀ v w, (β - lam • g) v w = (β - lam • g) w v := by
          intro v w
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hβ v w, hg v w]
        have hγnn : ∀ v, 0 ≤ (β - lam • g) v v := by
          intro v
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          linarith [hmin v]
        have hγ0 : (β - lam • g) v₁ v₁ = 0 := by
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          linarith
        have h := form_eq_zero_of_nonneg hγsym hγnn hγ0 w
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
        linarith
      have hW₁neg : ∀ v ∈ W₁, v ≠ 0 → β v v < 0 := by
        intro v hv hv0
        rw [(hmemW₁ v).mp hv v]
        exact mul_neg_of_neg_of_pos hlam (hpos v hv0)
      have hW₁inv : ∀ v ∈ W₁, ρ v ∈ W₁ := by
        intro v hv
        rw [hmemW₁]
        intro w
        obtain ⟨w', rfl⟩ := (LinearMap.injective_iff_surjective.mp hρinj) w
        rw [hβρ, hgρ]
        exact (hmemW₁ v).mp hv w'
      have hW₁map : W₁.map ρ = W₁ := by
        refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
        · rintro _ ⟨v, hv, rfl⟩
          exact hW₁inv v hv
        · exact (Submodule.equivMapOfInjective ρ hρinj W₁).finrank_eq.symm
      -- the g-orthogonal complement
      set U : Submodule ℝ V := LinearMap.BilinForm.orthogonal g W₁ with hU
      have hmemU : ∀ u, u ∈ U ↔ ∀ v ∈ W₁, g v u = 0 := fun u => Iff.rfl
      have hdis : Disjoint W₁ U := by
        rw [Submodule.disjoint_def]
        intro x hx hxU
        by_contra hx0
        have h := hpos x hx0
        rw [(hmemU x).mp hxU x hx] at h
        exact lt_irrefl _ h
      have hker : LinearMap.ker g = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        by_contra hx0
        have h := hpos x hx0
        rw [LinearMap.mem_ker.mp hx, LinearMap.zero_apply] at h
        exact lt_irrefl _ h
      have hdim : finrank ℝ W₁ + finrank ℝ U = finrank ℝ V := by
        have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := g) W₁
        have h0 : finrank ℝ (W₁ ⊓ LinearMap.ker g : Submodule ℝ V) = 0 := by
          rw [hker, inf_bot_eq, finrank_bot]
        rw [h0, add_zero] at h
        exact h
      have hc : IsCompl W₁ U := ⟨hdis, codisjoint_iff.mpr (Submodule.eq_top_of_disjoint W₁ U hdim.ge hdis)⟩
      have hUinv : ∀ u ∈ U, ρ u ∈ U := by
        intro u hu
        rw [hmemU]
        intro v hv
        rw [← hW₁map] at hv
        obtain ⟨v', hv', rfl⟩ := hv
        rw [hgρ]
        exact (hmemU u).mp hu v' hv'
      have horth : ∀ a ∈ W₁, ∀ u ∈ U, β a u = 0 := by
        intro a ha u hu
        rw [(hmemW₁ a).mp ha u, (hmemU u).mp hu a ha, mul_zero]
      -- the induction hypothesis on U
      have hW₁pos : 0 < finrank ℝ W₁ := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        exact ⟨⟨v₁, hv₁W⟩, fun h => hv₁0 (congrArg Subtype.val h)⟩
      have hlt : finrank ℝ U < d := by omega
      obtain ⟨W₂, hW₂inv, hW₂neg, hW₂dim⟩ := ih (finrank ℝ U) hlt rfl
        (β.compl₁₂ U.subtype U.subtype) (g.compl₁₂ U.subtype U.subtype) (ρ.restrict hUinv)
        (fun v w => hβ _ _) (fun v w => hg _ _)
        (fun v hv => hpos _ fun h => hv (Subtype.ext h))
        (fun v w => hβρ _ _) (fun v w => hgρ _ _)
      refine ⟨W₁ ⊔ W₂.map U.subtype, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨c', hc'', rfl⟩ := hc'
        rw [map_add]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hW₁inv a ha))
          (Submodule.mem_sup_right ⟨ρ.restrict hUinv c', hW₂inv c' hc'', rfl⟩)
      · intro x hx hx0
        obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨c', hc'', rfl⟩ := hc'
        have h1 : β a (U.subtype c') = 0 := horth a ha _ c'.2
        have h2 : β (U.subtype c') a = 0 := by rw [hβ]; exact h1
        have e : β (a + U.subtype c') (a + U.subtype c') =
            β a a + β (U.subtype c') (U.subtype c') := by
          simp only [map_add, LinearMap.add_apply, h1, h2]
          ring
        rw [e]
        have ha0 : β a a ≤ 0 := by
          by_cases h : a = 0
          · simp [h]
          · exact (hW₁neg a ha h).le
        have hc0 : β (U.subtype c') (U.subtype c') ≤ 0 := by
          by_cases h : c' = 0
          · simp [h]
          · exact (hW₂neg c' hc'' h).le
        by_cases h : a = 0
        · have hc'0 : c' ≠ 0 := by
            intro h'
            apply hx0
            rw [h, h', map_zero, add_zero]
          have := hW₂neg c' hc'' hc'0
          have this' : β (U.subtype c') (U.subtype c') < 0 := this
          linarith
        · have := hW₁neg a ha h
          linarith
      · -- the dimension
        have hinf : W₁ ⊓ W₂.map U.subtype = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨hx1, c', -, rfl⟩ := hx
          exact (Submodule.disjoint_def.mp hdis) _ hx1 c'.2
        have hsum := Submodule.finrank_sup_add_finrank_inf_eq W₁ (W₂.map U.subtype)
        rw [hinf, finrank_bot, add_zero, Submodule.finrank_map_subtype_eq] at hsum
        have hWneg : ((-(LinearMap.BilinMap.toQuadraticMap β)).restrict
            (W₁ ⊔ W₂.map U.subtype)).PosDef := by
          intro x hx
          have hx0 : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
          have hneg : β (x : V) (x : V) < 0 := by
            obtain ⟨a, ha, c, hc', hxe⟩ := Submodule.mem_sup.mp x.2
            obtain ⟨c', hc'', rfl⟩ := hc'
            have h1 : β a (U.subtype c') = 0 := horth a ha _ c'.2
            have h2 : β (U.subtype c') a = 0 := by rw [hβ]; exact h1
            have e : β (a + U.subtype c') (a + U.subtype c') =
                β a a + β (U.subtype c') (U.subtype c') := by
              simp only [map_add, LinearMap.add_apply, h1, h2]
              ring
            rw [← hxe, e]
            have ha0 : β a a ≤ 0 := by
              by_cases h : a = 0
              · simp [h]
              · exact (hW₁neg a ha h).le
            have hc0 : β (U.subtype c') (U.subtype c') ≤ 0 := by
              by_cases h : c' = 0
              · simp [h]
              · exact (hW₂neg c' hc'' h).le
            by_cases h : a = 0
            · have hc'0 : c' ≠ 0 := by
                intro h'
                apply hx0
                rw [← hxe, h, h', map_zero, add_zero]
              have this' : β (U.subtype c') (U.subtype c') < 0 := hW₂neg c' hc'' hc'0
              linarith
            · have := hW₁neg a ha h
              linarith
          change 0 < -(β (x : V) (x : V))
          linarith
        have hle := le_sigNeg_of_negDef (LinearMap.BilinMap.toQuadraticMap β) hWneg
        have hequiv : QuadraticMap.Equivalent
            (((LinearMap.BilinMap.toQuadraticMap β).restrict W₁).prod
              ((LinearMap.BilinMap.toQuadraticMap β).restrict U))
            (LinearMap.BilinMap.toQuadraticMap β) :=
          ⟨⟨Submodule.prodEquivOfIsCompl W₁ U hc, fun x => by
            change LinearMap.BilinMap.toQuadraticMap β
              (Submodule.prodEquivOfIsCompl W₁ U hc x) = _
            have h1 : β (x.1 : V) (x.2 : V) = 0 := horth _ x.1.2 _ x.2.2
            have h2 : β (x.2 : V) (x.1 : V) = 0 := by rw [hβ]; exact h1
            rw [Submodule.coe_prodEquivOfIsCompl', QuadraticMap.prod_apply, restrict_apply,
              restrict_apply]
            change β ((x.1 : V) + (x.2 : V)) ((x.1 : V) + (x.2 : V)) =
              β (x.1 : V) (x.1 : V) + β (x.2 : V) (x.2 : V)
            simp only [map_add, LinearMap.add_apply, h1, h2]
            ring⟩⟩
        have hadd : sigNeg (LinearMap.BilinMap.toQuadraticMap β) =
            sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict W₁) +
              sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict U) := by
          rw [← hequiv.sigNeg_eq, QuadraticForm.sigNeg_prod]
        have h1 : sigNeg ((LinearMap.BilinMap.toQuadraticMap β).restrict W₁) ≤ finrank ℝ W₁ := by
          rw [← sigPos_neg]
          exact sigPos_le_finrank _
        have h2 : (LinearMap.BilinMap.toQuadraticMap β).restrict U =
            LinearMap.BilinMap.toQuadraticMap (β.compl₁₂ U.subtype U.subtype) :=
          QuadraticMap.ext fun x => rfl
        rw [h2, ← hW₂dim] at hadd
        omega

end

end Finsler.InvariantNegative
