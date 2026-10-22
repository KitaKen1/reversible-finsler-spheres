module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Reduction to the kernel at a zero of a map with symmetric derivative, with no nondegeneracy
assumption. Let `G` be `C^k` at `p` with `G p = 0` and symmetric derivative `A` on a
finite-dimensional real inner product space, and let `P` be the orthogonal projection onto
`ker A`. The map `z ↦ P z + (1 - P) (G (p + z))` has the invertible derivative `P + A` at `0`.
Its local inverse `σ` satisfies `P (σ w) = P w` and `(1 - P) (G (p + σ w)) = (1 - P) w` near
`0`. Hence `σ` maps the kernel near `0` onto the points `z` near `0` at which `G (p + z)` lies
in the kernel, and all zeros of `G` near `p` are of this form. If `G` is the gradient of a
function `f`, the derivative of `w ↦ f (p + σ w)` at a kernel point `w` near `0` is the inner
product with `G (p + σ w)` after projection to the kernel, and the derivative of
`w ↦ G (p + σ w)` at `0` vanishes on the kernel. This is the reduction step of a degenerate
splitting lemma; no normal form is asserted. -/

@[expose] public section

namespace Finsler.LyapunovSchmidt

open Filter
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Linear

variable (A : E →L[ℝ] E)

/-- The orthogonal projection onto the kernel, as an endomorphism. -/
def kerProj : E →L[ℝ] E := (LinearMap.ker A.toLinearMap).starProjection

/-- The complementary projection. -/
def cokerProj : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - kerProj A

theorem cokerProj_apply (v : E) : cokerProj A v = v - kerProj A v := rfl

theorem kerProj_add_cokerProj (v : E) : kerProj A v + cokerProj A v = v := by
  rw [cokerProj_apply]
  abel

theorem map_kerProj (v : E) : A (kerProj A v) = 0 :=
  LinearMap.mem_ker.mp ((LinearMap.ker A.toLinearMap).starProjection_apply_mem v)

theorem kerProj_of_map_eq_zero {v : E} (hv : A v = 0) : kerProj A v = v :=
  Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_ker.mpr hv)

theorem kerProj_kerProj (v : E) : kerProj A (kerProj A v) = kerProj A v :=
  kerProj_of_map_eq_zero A (map_kerProj A v)

theorem inner_kerProj (u v : E) : ⟪kerProj A u, v⟫ = ⟪u, kerProj A v⟫ :=
  Submodule.inner_starProjection_left_eq_right _ u v

theorem kerProj_cokerProj (v : E) : kerProj A (cokerProj A v) = 0 := by
  rw [cokerProj_apply, map_sub, kerProj_kerProj, sub_self]

theorem cokerProj_of_map_eq_zero {v : E} (hv : A v = 0) : cokerProj A v = 0 := by
  rw [cokerProj_apply, kerProj_of_map_eq_zero A hv, sub_self]

theorem map_eq_zero_of_cokerProj {v : E} (hv : cokerProj A v = 0) : A v = 0 := by
  have h : v = kerProj A v := sub_eq_zero.mp hv
  rw [h]
  exact map_kerProj A v

/-- The linearization of the auxiliary map. -/
def lin : E →L[ℝ] E := kerProj A + A

variable {A} (hs : A.toLinearMap.IsSymmetric)
include hs

theorem kerProj_map (v : E) : kerProj A (A v) = 0 := by
  refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hu' : A u = 0 := LinearMap.mem_ker.mp hu
  have h : ⟪A u, v⟫ = ⟪u, A v⟫ := hs u v
  rw [hu', inner_zero_left] at h
  exact h.symm

theorem cokerProj_map (v : E) : cokerProj A (A v) = A v := by
  rw [cokerProj_apply, kerProj_map hs, sub_zero]

theorem lin_injective : Function.Injective (lin A) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h1 : kerProj A z + A z = 0 := hz
  have h2 : kerProj A z = 0 := by
    have h := congrArg (kerProj A) h1
    rwa [map_add, kerProj_kerProj, kerProj_map hs, add_zero, map_zero] at h
  have h3 : A z = 0 := by rwa [h2, zero_add] at h1
  rw [← kerProj_of_map_eq_zero A h3, h2]

/-- The linearization as a continuous linear equivalence. -/
def linEquiv : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (lin A).toLinearMap (lin_injective hs)).toContinuousLinearEquiv

theorem linEquiv_apply (z : E) : linEquiv hs z = kerProj A z + A z := rfl

theorem coe_linEquiv : (linEquiv hs : E →L[ℝ] E) = kerProj A + A :=
  ContinuousLinearMap.ext fun _ => rfl

theorem linEquiv_symm_of_map_eq_zero {w : E} (hw : A w = 0) : (linEquiv hs).symm w = w := by
  rw [ContinuousLinearEquiv.symm_apply_eq, linEquiv_apply, kerProj_of_map_eq_zero A hw, hw,
    add_zero]

theorem kerProj_linEquiv_symm (w : E) : kerProj A ((linEquiv hs).symm w) = kerProj A w := by
  have h1 : kerProj A ((linEquiv hs).symm w) + A ((linEquiv hs).symm w) = w := by
    rw [← linEquiv_apply hs, ContinuousLinearEquiv.apply_symm_apply]
  have h := congrArg (kerProj A) h1
  rwa [map_add, kerProj_kerProj, kerProj_map hs, add_zero] at h

theorem map_linEquiv_symm (w : E) : A ((linEquiv hs).symm w) = cokerProj A w := by
  have h1 : kerProj A ((linEquiv hs).symm w) + A ((linEquiv hs).symm w) = w := by
    rw [← linEquiv_apply hs, ContinuousLinearEquiv.apply_symm_apply]
  rw [cokerProj_apply, ← kerProj_linEquiv_symm hs w]
  exact eq_sub_of_add_eq' h1

end Linear

section Reduction

variable {A : E →L[ℝ] E} (hs : A.toLinearMap.IsSymmetric) {G : E → E} {p : E}

/-- The auxiliary map whose local inverse parametrizes the reduction. -/
def aux (G : E → E) (p : E) (A : E →L[ℝ] E) (z : E) : E :=
  kerProj A z + cokerProj A (G (p + z))

theorem aux_zero (hp : G p = 0) : aux G p A 0 = 0 := by
  rw [aux, add_zero, hp, map_zero, map_zero, add_zero]

theorem aux_contDiffAt {k : WithTop ℕ∞} (hG : ContDiffAt ℝ k G p) :
    ContDiffAt ℝ k (aux G p A) 0 := by
  have hG' : ContDiffAt ℝ k G (p + 0) := by rwa [add_zero]
  have h1 : ContDiffAt ℝ k (fun z : E => G (p + z)) 0 :=
    hG'.comp 0 (contDiffAt_const.add contDiffAt_id)
  exact (kerProj A).contDiff.contDiffAt.add ((cokerProj A).contDiff.contDiffAt.comp 0 h1)

include hs in
theorem aux_hasFDerivAt (hA : HasFDerivAt G A p) :
    HasFDerivAt (aux G p A) (linEquiv hs : E →L[ℝ] E) 0 := by
  have hA' : HasFDerivAt G A (p + 0) := by rwa [add_zero]
  have h1 : HasFDerivAt (fun z : E => G (p + z)) A 0 := (hasFDerivAt_comp_add_left p).mpr hA'
  have h2 : HasFDerivAt (aux G p A) (kerProj A + (cokerProj A).comp A) 0 :=
    (kerProj A).hasFDerivAt.add ((cokerProj A).hasFDerivAt.comp 0 h1)
  have h3 : kerProj A + (cokerProj A).comp A = (linEquiv hs : E →L[ℝ] E) := by
    rw [coe_linEquiv]
    refine ContinuousLinearMap.ext fun v => ?_
    change kerProj A v + cokerProj A (A v) = kerProj A v + A v
    rw [cokerProj_map hs]
  rwa [h3] at h2

include hs in
/-- The reduction map. Its projection to the kernel is the projection of the argument, and the
complementary component of `G` along it is the complementary component of the argument. -/
theorem exists_reduction {k : WithTop ℕ∞} (hk : k ≠ 0) (hG : ContDiffAt ℝ k G p)
    (hA : HasFDerivAt G A p) (hp : G p = 0) :
    ∃ σ : E → E, ContDiffAt ℝ k σ 0 ∧ σ 0 = 0 ∧
      HasStrictFDerivAt σ ((linEquiv hs).symm : E →L[ℝ] E) 0 ∧
      (∀ᶠ w in 𝓝 (0 : E), kerProj A (σ w) = kerProj A w ∧
        cokerProj A (G (p + σ w)) = cokerProj A w) ∧
      ∀ᶠ z in 𝓝 (0 : E), σ (kerProj A z + cokerProj A (G (p + z))) = z := by
  have hc : ContDiffAt ℝ k (aux G p A) 0 := aux_contDiffAt hG
  have hd : HasFDerivAt (aux G p A) (linEquiv hs : E →L[ℝ] E) 0 := aux_hasFDerivAt hs hA
  have h0 : aux G p A 0 = 0 := aux_zero hp
  have hstrict : HasStrictFDerivAt (aux G p A) (linEquiv hs : E →L[ℝ] E) 0 :=
    hc.hasStrictFDerivAt' hd hk
  refine ⟨hc.localInverse hd hk, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hc.to_localInverse hd hk
    rwa [h0] at h
  · have h := hc.localInverse_apply_image hd hk
    rwa [h0] at h
  · have h := hstrict.to_localInverse
    rwa [h0] at h
  · have hr := hstrict.eventually_right_inverse
    rw [h0] at hr
    filter_upwards [hr] with w hw
    have hw' : kerProj A (hc.localInverse hd hk w) +
        cokerProj A (G (p + hc.localInverse hd hk w)) = w := hw
    have h1 : kerProj A (hc.localInverse hd hk w) = kerProj A w := by
      have h := congrArg (kerProj A) hw'
      rwa [map_add, kerProj_kerProj, kerProj_cokerProj, add_zero] at h
    refine ⟨h1, ?_⟩
    rw [cokerProj_apply A w, ← h1]
    exact eq_sub_of_add_eq' hw'
  · exact hstrict.eventually_left_inverse

include hs in
/-- The reduction on the kernel: the reduction map sends kernel points near `0` to points whose
kernel projection is the given point and at which `G` lies in the kernel; every point near `0`
at which `G` lies in the kernel is obtained in this way; the derivative of the reduction map at
`0` is the identity on the kernel, and the derivative of the reduced map vanishes there. -/
theorem exists_reduction_ker {k : WithTop ℕ∞} (hk : k ≠ 0) (hG : ContDiffAt ℝ k G p)
    (hA : HasFDerivAt G A p) (hp : G p = 0) :
    ∃ σ : E → E, ContDiffAt ℝ k σ 0 ∧ σ 0 = 0 ∧
      (∀ w, A w = 0 → fderiv ℝ σ 0 w = w) ∧
      (∀ᶠ w in 𝓝 (0 : E), kerProj A (σ w) = kerProj A w) ∧
      (∀ᶠ w in 𝓝 (0 : E), A w = 0 → kerProj A (σ w) = w ∧ A (G (p + σ w)) = 0) ∧
      (∀ᶠ z in 𝓝 (0 : E), A (G (p + z)) = 0 → σ (kerProj A z) = z) ∧
      ContDiffAt ℝ k (fun w => G (p + σ w)) 0 ∧
      ∀ w, A w = 0 → fderiv ℝ (fun w => G (p + σ w)) 0 w = 0 := by
  obtain ⟨σ, hσ, hσ0, hσd, hr, hl⟩ := exists_reduction hs hk hG hA hp
  have hG' : ContDiffAt ℝ k G (p + σ 0) := by rwa [hσ0, add_zero]
  have hA' : HasFDerivAt G A (p + σ 0) := by rwa [hσ0, add_zero]
  have hσd' : HasFDerivAt (fun w => p + σ w) ((linEquiv hs).symm : E →L[ℝ] E) 0 :=
    hσd.hasFDerivAt.const_add p
  refine ⟨σ, hσ, hσ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hσd.hasFDerivAt.fderiv]
    exact linEquiv_symm_of_map_eq_zero hs hw
  · exact hr.mono fun w hw => hw.1
  · filter_upwards [hr] with w hw hAw
    refine ⟨by rw [hw.1, kerProj_of_map_eq_zero A hAw], ?_⟩
    refine map_eq_zero_of_cokerProj A ?_
    rw [hw.2, cokerProj_of_map_eq_zero A hAw]
  · filter_upwards [hl] with z hz hAz
    rw [cokerProj_of_map_eq_zero A hAz, add_zero] at hz
    exact hz
  · exact hG'.comp 0 (contDiffAt_const.add hσ)
  · intro w hw
    have h : HasFDerivAt (fun w => G (p + σ w))
        (A.comp ((linEquiv hs).symm : E →L[ℝ] E)) 0 := hA'.comp 0 hσd'
    rw [h.fderiv]
    change A ((linEquiv hs).symm w) = 0
    rw [map_linEquiv_symm hs, cokerProj_of_map_eq_zero A hw]

include hs in
/-- The reduced function. If `G` is the gradient of `f` near `p`, then at kernel points near `0`
the derivative of `w ↦ f (p + σ w)` is the inner product with `G (p + σ w)`, which lies in the
kernel, after projection of the direction to the kernel. -/
theorem exists_reduced_function {k : WithTop ℕ∞} (hk : k ≠ 0) (hG : ContDiffAt ℝ k G p)
    (hA : HasFDerivAt G A p) (hp : G p = 0) {f : E → ℝ}
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x) :
    ∃ σ : E → E, ContDiffAt ℝ k σ 0 ∧ σ 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0 : E), A w = 0 → kerProj A (σ w) = w ∧ A (G (p + σ w)) = 0) ∧
      (∀ᶠ z in 𝓝 (0 : E), A (G (p + z)) = 0 → σ (kerProj A z) = z) ∧
      ∀ᶠ w in 𝓝 (0 : E), A w = 0 →
        HasFDerivAt (fun w => f (p + σ w))
          ((innerSL ℝ (G (p + σ w))).comp (kerProj A)) w := by
  obtain ⟨σ, hσ, hσ0, hσd, hr, hl⟩ := exists_reduction hs hk hG hA hp
  have h1 : ContDiffAt ℝ 1 σ 0 := hσ.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hk)
  have hdiff : ∀ᶠ w in 𝓝 (0 : E), DifferentiableAt ℝ σ w :=
    (h1.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have htend : Tendsto (fun w => p + σ w) (𝓝 (0 : E)) (𝓝 p) := by
    have h : ContinuousAt (fun w => p + σ w) 0 := continuousAt_const.add hσ.continuousAt
    have h' := h.tendsto
    rwa [hσ0, add_zero] at h'
  have hfσ : ∀ᶠ w in 𝓝 (0 : E), HasFDerivAt f (innerSL ℝ (G (p + σ w))) (p + σ w) :=
    htend.eventually hf
  refine ⟨σ, hσ, hσ0, ?_, ?_, ?_⟩
  · filter_upwards [hr] with w hw hAw
    refine ⟨by rw [hw.1, kerProj_of_map_eq_zero A hAw], ?_⟩
    refine map_eq_zero_of_cokerProj A ?_
    rw [hw.2, cokerProj_of_map_eq_zero A hAw]
  · filter_upwards [hl] with z hz hAz
    rw [cokerProj_of_map_eq_zero A hAz, add_zero] at hz
    exact hz
  · filter_upwards [hdiff, hfσ, hr.eventually_nhds] with w hdw hfw hrw hAw
    have hσw : HasFDerivAt σ (fderiv ℝ σ w) w := hdw.hasFDerivAt
    have hproj : (kerProj A).comp (fderiv ℝ σ w) = kerProj A := by
      have ha : HasFDerivAt (fun w => kerProj A (σ w)) ((kerProj A).comp (fderiv ℝ σ w)) w :=
        (kerProj A).hasFDerivAt.comp w hσw
      have hb : HasFDerivAt (fun w => kerProj A (σ w)) (kerProj A) w :=
        (kerProj A).hasFDerivAt.congr_of_eventuallyEq (hrw.mono fun y hy => hy.1)
      exact ha.unique hb
    have hker : kerProj A (G (p + σ w)) = G (p + σ w) := by
      have h := hrw.self_of_nhds.2
      rw [cokerProj_of_map_eq_zero A hAw] at h
      exact (sub_eq_zero.mp h).symm
    have hchain : HasFDerivAt (fun w => f (p + σ w))
        ((innerSL ℝ (G (p + σ w))).comp (fderiv ℝ σ w)) w :=
      hfw.comp w (hσw.const_add p)
    have heq : (innerSL ℝ (G (p + σ w))).comp (fderiv ℝ σ w) =
        (innerSL ℝ (G (p + σ w))).comp (kerProj A) := by
      refine ContinuousLinearMap.ext fun η => ?_
      change ⟪G (p + σ w), fderiv ℝ σ w η⟫ = ⟪G (p + σ w), kerProj A η⟫
      have hη : kerProj A (fderiv ℝ σ w η) = kerProj A η :=
        congrArg (fun L : E →L[ℝ] E => L η) hproj
      calc ⟪G (p + σ w), fderiv ℝ σ w η⟫
          = ⟪kerProj A (G (p + σ w)), fderiv ℝ σ w η⟫ := by rw [hker]
        _ = ⟪G (p + σ w), kerProj A (fderiv ℝ σ w η)⟫ := inner_kerProj A _ _
        _ = ⟪G (p + σ w), kerProj A η⟫ := by rw [hη]
    rwa [heq] at hchain

end Reduction

end

end Finsler.LyapunovSchmidt
