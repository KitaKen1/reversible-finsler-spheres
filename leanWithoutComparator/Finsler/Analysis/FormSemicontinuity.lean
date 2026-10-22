module

public import Finsler.Analysis.FrameIndex
public import Mathlib.Topology.LocallyConstant.Basic

/-! Semicontinuity of the indices of inertia. A negative frame of b vectors for a bilinear
function on a finite dimensional real normed space bounds the negative index of inertia of its
quadratic form from below by b. Since negativity of a fixed frame is an open condition in a
continuous family of bilinear functions, the negative index of inertia is lower semicontinuous
in the parameter, and so is the positive index. The radical of the quadratic form of a symmetric
bilinear function is its kernel, so the dimension of the kernel is the dimension of the space
minus the two indices: it is upper semicontinuous. If the dimension of the kernel is constant
on a preconnected parameter space, the negative index of inertia is constant. -/

@[expose] public section

namespace Finsler.FormSemicontinuity

open Module QuadraticForm QuadraticMap Finsler.DefiniteFrames Finsler.FrameIndex
open scoped Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {b : ℕ}

/-- A negative frame of b vectors bounds the negative index of inertia from below. -/
theorem le_sigNeg_of_neg {β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {G : Fin b → V} (hG : Neg β G) :
    b ≤ sigNeg (LinearMap.BilinMap.toQuadraticMap β) := by
  have hli := linearIndependent_of_neg hG
  set W : Submodule ℝ V := Submodule.span ℝ (Set.range G) with hWdef
  have hrank : finrank ℝ W = b := by
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
    have h1 := hG u hu0
    have h2 : comb G u = (x : V) := hu
    rw [h2] at h1
    change 0 < -(β (x : V) (x : V))
    linarith
  have hle := le_sigNeg_of_negDef (LinearMap.BilinMap.toQuadraticMap β) hdef
  rwa [hrank] at hle

omit [FiniteDimensional ℝ V] in
/-- The radical of the quadratic form of a symmetric bilinear function is its kernel. -/
theorem radical_eq_ker {β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hsym : ∀ v w, β v w = β w v) :
    (LinearMap.BilinMap.toQuadraticMap β).radical = LinearMap.ker β := by
  ext m
  rw [QuadraticMap.mem_radical_iff', LinearMap.mem_ker]
  constructor
  · rintro ⟨h0, h⟩
    refine LinearMap.ext fun x => ?_
    have h1 := h x
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply] at h1 h0
    rw [h0, hsym x m] at h1
    simp only [LinearMap.zero_apply]
    linarith
  · intro h
    have hm : ∀ x, β m x = 0 := fun x => by
      rw [h]
      rfl
    refine ⟨?_, fun x => ?_⟩
    · simp only [LinearMap.BilinMap.toQuadraticMap_apply]
      exact hm m
    · simp only [LinearMap.BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply, hm,
        hsym x m, zero_add]

/-- The two indices of inertia and the dimension of the kernel of a symmetric bilinear function
add up to the dimension of the space. -/
theorem sigPos_add_sigNeg_add_ker {β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hsym : ∀ v w, β v w = β w v) :
    sigPos (LinearMap.BilinMap.toQuadraticMap β) + sigNeg (LinearMap.BilinMap.toQuadraticMap β) +
      finrank ℝ (LinearMap.ker β) = finrank ℝ V := by
  rw [← radical_eq_ker hsym]
  exact sigPos_add_sigNeg_add_radical

variable {Θ : Type*} [TopologicalSpace Θ] {B : Θ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

/-- The negative index of inertia of a continuous family of bilinear functions is lower
semicontinuous. -/
theorem isOpen_le_sigNeg (hB : Continuous fun p : Θ × V × V => B p.1 p.2.1 p.2.2) (b : ℕ) :
    IsOpen {θ : Θ | b ≤ sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ))} := by
  rw [isOpen_iff_mem_nhds]
  intro θ₀ hθ₀
  obtain ⟨G, hG⟩ := exists_neg_frame (B θ₀) rfl
  have hopen := isOpen_neg B hB (isCompact_singleton (x := PUnit.unit.{1}))
    (fun _ : Θ × PUnit.{1} => G) continuous_const
  have hmem : θ₀ ∈ {θ : Θ | ∀ y ∈ ({PUnit.unit} : Set PUnit.{1}), Neg (B θ) G} := fun _ _ => hG
  filter_upwards [hopen.mem_nhds hmem] with θ hθ
  exact le_trans hθ₀ (le_sigNeg_of_neg (hθ PUnit.unit rfl))

/-- The positive index of inertia of a continuous family of bilinear functions is lower
semicontinuous. -/
theorem isOpen_le_sigPos (hB : Continuous fun p : Θ × V × V => B p.1 p.2.1 p.2.2) (b : ℕ) :
    IsOpen {θ : Θ | b ≤ sigPos (LinearMap.BilinMap.toQuadraticMap (B θ))} := by
  have hB' : Continuous fun p : Θ × V × V => (-B p.1) p.2.1 p.2.2 := by
    have h := hB.neg
    exact h
  have h := isOpen_le_sigNeg (B := fun θ => -B θ) hB' b
  have he : ∀ θ, sigNeg (LinearMap.BilinMap.toQuadraticMap (-B θ)) =
      sigPos (LinearMap.BilinMap.toQuadraticMap (B θ)) := fun θ => by
    rw [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg]
  simpa only [he] using h

/-- The dimension of the kernel of a continuous family of symmetric bilinear functions is upper
semicontinuous. -/
theorem isOpen_finrank_ker_le (hB : Continuous fun p : Θ × V × V => B p.1 p.2.1 p.2.2)
    (hsym : ∀ θ v w, B θ v w = B θ w v) (k : ℕ) :
    IsOpen {θ : Θ | finrank ℝ (LinearMap.ker (B θ)) ≤ k} := by
  rw [isOpen_iff_mem_nhds]
  intro θ₀ hθ₀
  have hθ₀' : finrank ℝ (LinearMap.ker (B θ₀)) ≤ k := hθ₀
  filter_upwards [(isOpen_le_sigNeg hB _).mem_nhds
      (le_refl (sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ₀)))),
    (isOpen_le_sigPos hB _).mem_nhds
      (le_refl (sigPos (LinearMap.BilinMap.toQuadraticMap (B θ₀))))] with θ h1 h2
  have h1' : sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ₀)) ≤
      sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ)) := h1
  have h2' : sigPos (LinearMap.BilinMap.toQuadraticMap (B θ₀)) ≤
      sigPos (LinearMap.BilinMap.toQuadraticMap (B θ)) := h2
  have e₀ := sigPos_add_sigNeg_add_ker (hsym θ₀)
  have e := sigPos_add_sigNeg_add_ker (hsym θ)
  change finrank ℝ (LinearMap.ker (B θ)) ≤ k
  omega

/-- If the dimension of the kernel of a continuous family of symmetric bilinear functions is
constant, the negative index of inertia is locally constant. -/
theorem eventually_sigNeg_eq (hB : Continuous fun p : Θ × V × V => B p.1 p.2.1 p.2.2)
    (hsym : ∀ θ v w, B θ v w = B θ w v)
    (hk : ∀ θ θ', finrank ℝ (LinearMap.ker (B θ)) = finrank ℝ (LinearMap.ker (B θ'))) (θ₀ : Θ) :
    ∀ᶠ θ in 𝓝 θ₀, sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ)) =
      sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ₀)) := by
  filter_upwards [(isOpen_le_sigNeg hB _).mem_nhds
      (le_refl (sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ₀)))),
    (isOpen_le_sigPos hB _).mem_nhds
      (le_refl (sigPos (LinearMap.BilinMap.toQuadraticMap (B θ₀))))] with θ h1 h2
  have h1' : sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ₀)) ≤
      sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ)) := h1
  have h2' : sigPos (LinearMap.BilinMap.toQuadraticMap (B θ₀)) ≤
      sigPos (LinearMap.BilinMap.toQuadraticMap (B θ)) := h2
  have e₀ := sigPos_add_sigNeg_add_ker (hsym θ₀)
  have e := sigPos_add_sigNeg_add_ker (hsym θ)
  have hk' := hk θ θ₀
  omega

/-- If the dimension of the kernel of a continuous family of symmetric bilinear functions on a
preconnected parameter space is constant, the negative index of inertia is constant. -/
theorem sigNeg_eq_of_finrank_ker_eq [PreconnectedSpace Θ]
    (hB : Continuous fun p : Θ × V × V => B p.1 p.2.1 p.2.2)
    (hsym : ∀ θ v w, B θ v w = B θ w v)
    (hk : ∀ θ θ', finrank ℝ (LinearMap.ker (B θ)) = finrank ℝ (LinearMap.ker (B θ')))
    (θ θ' : Θ) : sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ)) =
      sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ')) := by
  have hloc : IsLocallyConstant fun θ => sigNeg (LinearMap.BilinMap.toQuadraticMap (B θ)) :=
    (IsLocallyConstant.iff_eventually_eq _).mpr fun θ₀ => eventually_sigNeg_eq hB hsym hk θ₀
  exact hloc.apply_eq_of_preconnectedSpace θ θ'

end

end Finsler.FormSemicontinuity
