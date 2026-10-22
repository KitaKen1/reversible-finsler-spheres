module

public import TauCeti.Analysis.ODE.GlobalSolution
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Flows on a product of unit spheres. For a vector field Y on a product of copies of a real
inner product space, the tangential field removes from every component the multiple of the
position vector: tang Y (Q)_j = Y(Q)_j − ⟪Y(Q)_j, Q_j⟫ Q_j. It is as smooth as Y and has compact
support if Y has. Along the global flow of a Lipschitz tangential field the squared norm u of a
component satisfies u' = −2 ⟪Y_j, Q_j⟫ (u − 1); so a component of norm one keeps norm one
(Grönwall), and the flow maps the product of the unit spheres into itself. If a function is
invariant under positive rescaling of the components, its derivative in the direction of the
tangential field at a point with unit components is its derivative in the direction Y. Along the
global solution of a Lipschitz field a function which is differentiable where the field does
not vanish and has nonpositive derivative in the direction of the field does not increase, and
it decreases strictly if that derivative is negative at the initial point. -/

@[expose] public section

namespace Finsler.SphereFlow

open Set Filter
open scoped Topology ContDiff NNReal RealInnerProductSpace

noncomputable section

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The tangential part of a field on a product: in every component the multiple of the
position vector is removed. -/
def tang (Y : (ι → H) → ι → H) (Q : ι → H) : ι → H :=
  fun j => Y Q j - ⟪Y Q j, Q j⟫ • Q j

theorem tang_apply (Y : (ι → H) → ι → H) (Q : ι → H) (j : ι) :
    tang Y Q j = Y Q j - ⟪Y Q j, Q j⟫ • Q j := rfl

/-- The radial component of the tangential field vanishes on the unit sphere. -/
theorem inner_tang (Y : (ι → H) → ι → H) (Q : ι → H) (j : ι) :
    ⟪Q j, tang Y Q j⟫ = ⟪Y Q j, Q j⟫ * (1 - ‖Q j‖ ^ 2) := by
  rw [tang_apply, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm (Y Q j) (Q j)]
  ring

variable [Fintype ι]

theorem tang_contDiff {k : WithTop ℕ∞} {Y : (ι → H) → ι → H} (hY : ContDiff ℝ k Y) :
    ContDiff ℝ k (tang Y) := by
  rw [contDiff_pi]
  intro j
  have h1 : ContDiff ℝ k fun Q : ι → H => Y Q j := (contDiff_apply ℝ H j).comp hY
  have h2 : ContDiff ℝ k fun Q : ι → H => Q j := contDiff_apply ℝ H j
  exact h1.sub ((h1.inner ℝ h2).smul h2)

omit [Fintype ι] in
theorem tang_hasCompactSupport {Y : (ι → H) → ι → H} (hY : HasCompactSupport Y) :
    HasCompactSupport (tang Y) := by
  refine hY.mono fun Q hQ => ?_
  by_contra h
  apply hQ
  have h0 : Y Q = 0 := by
    by_contra h'
    exact h h'
  funext j
  rw [tang_apply, h0]
  simp

variable [CompleteSpace H]

/-- Along the global flow of a Lipschitz tangential field a component of norm one keeps norm
one. -/
theorem norm_globalSolution {Y : (ι → H) → ι → H} (hYc : Continuous Y) {K : ℝ≥0}
    (hL : LipschitzWith K (tang Y)) (Q : ι → H) (j : ι) (hQ : ‖Q j‖ = 1) {t : ℝ}
    (ht : 0 ≤ t) : ‖ODE.globalSolution (tang Y) hL Q t j‖ = 1 := by
  set γ := ODE.globalSolution (tang Y) hL Q with hγdef
  have hγc : Continuous γ := ODE.continuous_globalSolution_apply (tang Y) hL Q
  have hγj : ∀ s, HasDerivAt (fun s => γ s j) (tang Y (γ s) j) s := fun s =>
    (hasDerivAt_pi.mp (ODE.hasDerivAt_globalSolution (tang Y) hL Q s)) j
  set u : ℝ → ℝ := fun s => ‖γ s j‖ ^ 2 - 1 with hu
  set c : ℝ → ℝ := fun s => ⟪Y (γ s) j, γ s j⟫ with hc
  have hud : ∀ s, HasDerivAt u (-(2 * c s) * u s) s := by
    intro s
    have h := ((hγj s).norm_sq).sub_const 1
    have he : 2 * ⟪γ s j, tang Y (γ s) j⟫ = -(2 * c s) * u s := by
      rw [inner_tang, hc, hu]
      ring
    rw [he] at h
    exact h
  have hcc : Continuous c :=
    ((continuous_apply j).comp (hYc.comp hγc)).inner ((continuous_apply j).comp hγc)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) t)
    hcc.continuousOn
  have huc : Continuous u := (((continuous_apply j).comp hγc).norm.pow 2).sub continuous_const
  have h0 : ‖u 0‖ ≤ 0 := by
    rw [hu]
    simp only [hγdef, ODE.globalSolution_zero, hQ]
    norm_num
  have hbound := norm_le_gronwallBound_of_norm_deriv_right_le (f := u)
    (f' := fun s => -(2 * c s) * u s) (δ := 0) (K := 2 * C) (ε := 0) (a := 0) (b := t)
    huc.continuousOn (fun s _ => (hud s).hasDerivWithinAt) h0 (fun s hs => by
      rw [add_zero, norm_mul, norm_neg, norm_mul, Real.norm_ofNat]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hC s ⟨hs.1, hs.2.le⟩) (by norm_num)) (norm_nonneg _))
    t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at hbound
  have hut : u t = 0 := norm_le_zero_iff.mp hbound
  have hsq : ‖γ t j‖ ^ 2 = 1 ^ 2 := by
    rw [hu] at hut
    have := sub_eq_zero.mp hut
    rw [this, one_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq

omit [CompleteSpace H] in
/-- For a function invariant under positive rescaling of one component, the derivative in the
direction of that component of the position vanishes. -/
theorem fderiv_single_eq_zero [DecidableEq ι] {f : (ι → H) → ℝ} {Q : ι → H} {j : ι}
    (hf : DifferentiableAt ℝ f Q)
    (hinv : ∀ᶠ s in 𝓝 (0 : ℝ), f (Q + s • (Pi.single j (Q j) : ι → H)) = f Q) :
    fderiv ℝ f Q ((Pi.single j (Q j) : ι → H)) = 0 := by
  have hline : HasDerivAt (fun s : ℝ => Q + s • (Pi.single j (Q j) : ι → H)) ((Pi.single j (Q j) : ι → H)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const ((Pi.single j (Q j) : ι → H))).const_add Q
    simpa using h
  have hcomp : HasDerivAt (fun s : ℝ => f (Q + s • (Pi.single j (Q j) : ι → H)))
      (fderiv ℝ f Q ((Pi.single j (Q j) : ι → H))) 0 := by
    have hfQ : HasFDerivAt f (fderiv ℝ f Q) (Q + (0 : ℝ) • (Pi.single j (Q j) : ι → H)) := by
      rw [zero_smul, add_zero]
      exact hf.hasFDerivAt
    exact hfQ.comp_hasDerivAt (0 : ℝ) hline
  have hconst : HasDerivAt (fun s : ℝ => f (Q + s • (Pi.single j (Q j) : ι → H))) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (f Q)).congr_of_eventuallyEq hinv
  exact hcomp.unique hconst

omit [CompleteSpace H] in
/-- If the derivative of a function vanishes in the direction of every component of the
position, its derivative in the direction of the tangential field is its derivative in the
direction of the field. -/
theorem fderiv_tang [DecidableEq ι] {f : (ι → H) → ℝ} {Q : ι → H}
    (hrad : ∀ j, fderiv ℝ f Q ((Pi.single j (Q j) : ι → H)) = 0) (Y : (ι → H) → ι → H) :
    fderiv ℝ f Q (tang Y Q) = fderiv ℝ f Q (Y Q) := by
  have he : tang Y Q = Y Q - ∑ j, ⟪Y Q j, Q j⟫ • (Pi.single j (Q j) : ι → H) := by
    funext i
    rw [tang_apply, Pi.sub_apply, Finset.sum_apply]
    congr 1
    rw [Finset.sum_eq_single i]
    · rw [Pi.smul_apply, Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [he, map_sub, map_sum]
  have hz : ∑ j, fderiv ℝ f Q (⟪Y Q j, Q j⟫ • (Pi.single j (Q j) : ι → H)) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [map_smul, hrad j, smul_zero]
  rw [hz, sub_zero]

section Along

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {X : E → E}
  {K : ℝ≥0} (hL : LipschitzWith K X)

/-- The global solution through a zero of the field is constant. -/
theorem globalSolution_of_zero {Q : E} (hQ : X Q = 0) (t : ℝ) :
    ODE.globalSolution X hL Q t = Q := by
  have h := ODE.eq_globalSolution X hL (γ := fun _ => Q) (fun t => by
    rw [hQ]
    exact hasDerivAt_const t Q)
  exact (congrFun h t).symm

/-- The field does not vanish along the global solution through a point where it does not
vanish. -/
theorem ne_zero_along {Q : E} (hQ : X Q ≠ 0) (s : ℝ) : X (ODE.globalSolution X hL Q s) ≠ 0 := by
  intro h0
  apply hQ
  have h1 := globalSolution_of_zero hL h0 (-s)
  rw [← ODE.globalSolution_add, add_neg_cancel, ODE.globalSolution_zero] at h1
  rw [h1]
  exact h0

/-- The derivative of a function along the global solution. -/
theorem hasDerivAt_along {f : E → ℝ} {Q : E} {s : ℝ}
    (hf : DifferentiableAt ℝ f (ODE.globalSolution X hL Q s)) :
    HasDerivAt (fun r => f (ODE.globalSolution X hL Q r))
      (fderiv ℝ f (ODE.globalSolution X hL Q s) (X (ODE.globalSolution X hL Q s))) s :=
  hf.hasFDerivAt.comp_hasDerivAt s (ODE.hasDerivAt_globalSolution X hL Q s)

/-- A function which is differentiable where the field does not vanish, with nonpositive
derivative in the direction of the field along the solution up to the time T, does not increase
along the solution up to the time T. -/
theorem antitoneOn_along {f : E → ℝ} {O : Set E} (hf : ∀ P ∈ O, DifferentiableAt ℝ f P)
    (hsupp : ∀ P, X P ≠ 0 → P ∈ O) {Q : E} {T : ℝ}
    (hsign : ∀ s ∈ Icc (0 : ℝ) T, ODE.globalSolution X hL Q s ∈ O →
      fderiv ℝ f (ODE.globalSolution X hL Q s) (X (ODE.globalSolution X hL Q s)) ≤ 0) :
    AntitoneOn (fun r => f (ODE.globalSolution X hL Q r)) (Icc 0 T) := by
  by_cases hQ : X Q = 0
  · intro r _ r' _ _
    change f (ODE.globalSolution X hL Q r') ≤ f (ODE.globalSolution X hL Q r)
    rw [globalSolution_of_zero hL hQ, globalSolution_of_zero hL hQ]
  · have hO : ∀ s, ODE.globalSolution X hL Q s ∈ O := fun s => hsupp _ (ne_zero_along hL hQ s)
    have hd : ∀ s, HasDerivAt (fun r => f (ODE.globalSolution X hL Q r))
        (fderiv ℝ f (ODE.globalSolution X hL Q s) (X (ODE.globalSolution X hL Q s))) s :=
      fun s => hasDerivAt_along hL (hf _ (hO s))
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [(hd s).deriv]
    exact hsign s (interior_subset hs) (hO s)

/-- If moreover the derivative in the direction of the field is negative at the initial point,
the function decreases strictly along the solution. -/
theorem lt_along {f : E → ℝ} {O : Set E} (hf : ∀ P ∈ O, DifferentiableAt ℝ f P)
    (hsupp : ∀ P, X P ≠ 0 → P ∈ O) {Q : E} {T : ℝ} (hT : 0 < T)
    (hsign : ∀ s ∈ Icc (0 : ℝ) T, ODE.globalSolution X hL Q s ∈ O →
      fderiv ℝ f (ODE.globalSolution X hL Q s) (X (ODE.globalSolution X hL Q s)) ≤ 0)
    (hneg : fderiv ℝ f Q (X Q) < 0) : f (ODE.globalSolution X hL Q T) < f Q := by
  have hQ : X Q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hneg
    exact lt_irrefl _ hneg
  have hQO : Q ∈ O := hsupp Q hQ
  have hanti := antitoneOn_along hL hf hsupp hsign
  have hd0 : HasDerivAt (fun r => f (ODE.globalSolution X hL Q r)) (fderiv ℝ f Q (X Q)) 0 := by
    have h := hasDerivAt_along hL (f := f) (Q := Q) (s := 0)
      (by rw [ODE.globalSolution_zero]; exact hf Q hQO)
    rwa [ODE.globalSolution_zero] at h
  have hsl := hasDerivAt_iff_tendsto_slope.mp hd0
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      slope (fun r => f (ODE.globalSolution X hL Q r)) 0 s < 0 :=
    (hsl.eventually (gt_mem_nhds hneg)).filter_mono
      (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  obtain ⟨s, hs, hsT⟩ := (hev.and (Ioc_mem_nhdsGT hT)).exists
  rw [slope_def_field, sub_zero, ODE.globalSolution_zero] at hs
  have hs0 : f (ODE.globalSolution X hL Q s) < f Q := by
    by_contra h
    have h' := not_lt.mp h
    have : 0 ≤ (f (ODE.globalSolution X hL Q s) - f Q) / s :=
      div_nonneg (sub_nonneg.mpr h') hsT.1.le
    linarith
  have h1 := hanti ⟨hsT.1.le, hsT.2⟩ ⟨hT.le, le_rfl⟩ hsT.2
  have h1' : f (ODE.globalSolution X hL Q T) ≤ f (ODE.globalSolution X hL Q s) := h1
  linarith

end Along

end

end Finsler.SphereFlow
