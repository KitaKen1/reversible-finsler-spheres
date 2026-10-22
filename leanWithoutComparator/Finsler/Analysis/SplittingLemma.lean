module

public import Finsler.Analysis.LyapunovSchmidt
public import Finsler.Analysis.Congruence
public import Finsler.Analysis.SegmentAverage

/-! The degenerate splitting lemma. Let `G` be `C²` at `p` on a finite-dimensional real inner
product space, with `G p = 0` and symmetric derivative `A`, and let `G` represent the derivative
of `f` near `p`. Let `P` be the orthogonal projection onto `ker A` and `σ` the reduction map of
`LyapunovSchmidt`. Then there is a map `Ξ`, `C¹` at `0`, with `Ξ 0 = 0` and strict derivative
the identity at `0`, such that near `0`

  `P (Ξ z) = P z`  and  `f (p + z) = f (p + σ (P z)) + ⟪A (Ξ z), Ξ z⟫ / 2`.

So in the coordinates `Ξ` the function is the sum of the reduced function on the kernel and the
quadratic form of `A`; no nondegeneracy is assumed. If `A` is injective this is the Morse lemma
with a `C¹` chart for a function whose gradient is `C²`.

Proof. In the coordinates `w` of the reduction map, the derivative of `f (p + σ w)` in a
transverse direction `Q η` is `⟪Q w, Dσ(w) (Q η)⟫`. Integration along the segment from `P w` to
`w` gives `f (p + σ w) - f (p + σ (P w)) = ⟪Q w, B(w) (Q w)⟫` with the average `B(w)` of `Dσ`,
which is `C¹` and equals `(P + A)⁻¹ / 2` at `0`. The symmetric operators `S(w)` of the forms
`x ↦ |P x|² + 2 ⟪B(w) Q x, Q x⟫` are congruent to `S(0) = (P + A)⁻¹` by operators `R(w)` that
commute with `P - Q` (`Congruence`). With `ξ = (P + A)⁻¹ R(w) Q w` this gives
`⟪Q w, B(w) Q w⟫ = ⟪ξ, A ξ⟫ / 2`, and `Ξ z = P w + ξ` for `w = P z + Q (G (p + z))`. -/

@[expose] public section

namespace Finsler.SplittingLemma

open Filter Set MeasureTheory
open Finsler.LyapunovSchmidt Finsler.SegmentAverage Finsler.Congruence
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Projections, the reflection and symmetrization -/

section Linear

variable (A : E →L[ℝ] E)

theorem cokerProj_kerProj (v : E) : cokerProj A (kerProj A v) = 0 := by
  rw [cokerProj_apply, kerProj_kerProj, sub_self]

theorem cokerProj_cokerProj (v : E) : cokerProj A (cokerProj A v) = cokerProj A v := by
  rw [cokerProj_apply A (cokerProj A v), kerProj_cokerProj, sub_zero]

theorem inner_cokerProj (u v : E) : ⟪cokerProj A u, v⟫ = ⟪u, cokerProj A v⟫ := by
  rw [cokerProj_apply, cokerProj_apply, inner_sub_left, inner_sub_right, inner_kerProj]

/-- The reflection in the kernel: the identity on the kernel and minus the identity on its
orthogonal complement. -/
def refl : E →L[ℝ] E := kerProj A - cokerProj A

theorem refl_apply (x : E) : refl A x = kerProj A x - cokerProj A x := rfl

theorem refl_refl (x : E) : refl A (refl A x) = x := by
  rw [refl_apply, refl_apply]
  simp only [map_sub, kerProj_kerProj, kerProj_cokerProj, cokerProj_kerProj,
    cokerProj_cokerProj, sub_zero, zero_sub, sub_neg_eq_add]
  exact kerProj_add_cokerProj A x

/-- The reflection as a continuous linear equivalence. -/
def reflEquiv : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (refl A) (refl A) (refl_refl A) (refl_refl A)

theorem reflEquiv_apply (x : E) : reflEquiv A x = kerProj A x - cokerProj A x := rfl

/-- The adjoint as a continuous real-linear map of operators. -/
def adjL : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.mkContinuous
    { toFun := fun T => ContinuousLinearMap.adjoint T
      map_add' := fun S T => map_add _ S T
      map_smul' := fun c T => by
        rw [map_smulₛₗ]
        simp }
    1 (fun T => by
      rw [one_mul]
      exact (LinearIsometryEquiv.norm_map _ T).le)

theorem adjL_inner_left (T : E →L[ℝ] E) (x y : E) : ⟪adjL T x, y⟫ = ⟪x, T y⟫ :=
  ContinuousLinearMap.adjoint_inner_left T y x

theorem adjL_inner_right (T : E →L[ℝ] E) (x y : E) : ⟪x, adjL T y⟫ = ⟪T x, y⟫ :=
  ContinuousLinearMap.adjoint_inner_right T x y

/-- The symmetric operator of the quadratic form `x ↦ ⟪P x, P x⟫ + ⟪T (Q x), Q x⟫`. -/
def sym (T : E →L[ℝ] E) : E →L[ℝ] E :=
  kerProj A + (cokerProj A).comp (((1 / 2 : ℝ) • (T + adjL T)).comp (cokerProj A))

theorem sym_apply (T : E →L[ℝ] E) (x : E) :
    sym A T x = kerProj A x +
      cokerProj A ((1 / 2 : ℝ) • (T (cokerProj A x) + adjL T (cokerProj A x))) := rfl

theorem inner_sym (T : E →L[ℝ] E) (x x' : E) : ⟪sym A T x, x'⟫ = ⟪x, sym A T x'⟫ := by
  have h1 : ⟪cokerProj A ((1 / 2 : ℝ) • (T (cokerProj A x) + adjL T (cokerProj A x))), x'⟫ =
      1 / 2 * (⟪T (cokerProj A x), cokerProj A x'⟫ + ⟪cokerProj A x, T (cokerProj A x')⟫) := by
    rw [inner_cokerProj, real_inner_smul_left, inner_add_left, adjL_inner_left]
  have h2 : ⟪x, cokerProj A ((1 / 2 : ℝ) • (T (cokerProj A x') + adjL T (cokerProj A x')))⟫ =
      1 / 2 * (⟪cokerProj A x, T (cokerProj A x')⟫ + ⟪T (cokerProj A x), cokerProj A x'⟫) := by
    rw [← inner_cokerProj, real_inner_smul_right, inner_add_right, adjL_inner_right]
  rw [sym_apply, sym_apply, inner_add_left, inner_add_right, h1, h2, inner_kerProj]
  ring

/-- On the orthogonal complement of the kernel the form of `sym A T` is the form of `T`. -/
theorem inner_sym_cokerProj (T : E →L[ℝ] E) (w : E) :
    ⟪sym A T (cokerProj A w), cokerProj A w⟫ = ⟪T (cokerProj A w), cokerProj A w⟫ := by
  rw [sym_apply, kerProj_cokerProj, zero_add, cokerProj_cokerProj, inner_cokerProj,
    cokerProj_cokerProj, real_inner_smul_left, inner_add_left, adjL_inner_left,
    real_inner_comm (T (cokerProj A w)) (cokerProj A w)]
  ring

/-- The symmetrized operators commute with the reflection. -/
theorem sym_refl (T : E →L[ℝ] E) (x : E) :
    sym A T (reflEquiv A x) = reflEquiv A (sym A T x) := by
  have h1 : kerProj A (reflEquiv A x) = kerProj A x := by
    rw [reflEquiv_apply, map_sub, kerProj_kerProj, kerProj_cokerProj, sub_zero]
  have h2 : cokerProj A (reflEquiv A x) = -cokerProj A x := by
    rw [reflEquiv_apply, map_sub, cokerProj_kerProj, cokerProj_cokerProj, zero_sub]
  have h3 : kerProj A (sym A T x) = kerProj A x := by
    rw [sym_apply, map_add, kerProj_kerProj, kerProj_cokerProj, add_zero]
  have h4 : cokerProj A (sym A T x) =
      cokerProj A ((1 / 2 : ℝ) • (T (cokerProj A x) + adjL T (cokerProj A x))) := by
    rw [sym_apply, map_add, cokerProj_kerProj, cokerProj_cokerProj, zero_add]
  rw [reflEquiv_apply A (sym A T x), h3, h4, sym_apply, h1, h2, map_neg, map_neg, ← neg_add,
    smul_neg, map_neg, sub_eq_add_neg]

theorem sym_contDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {T : X → E →L[ℝ] E} {x : X} {n : WithTop ℕ∞} (hT : ContDiffAt ℝ n T x) :
    ContDiffAt ℝ n (fun w => sym A (T w)) x :=
  contDiffAt_const.add (contDiffAt_const.clm_comp
    (((hT.add ((adjL (E := E)).contDiff.contDiffAt.comp x hT)).const_smul (1 / 2 : ℝ)).clm_comp
      contDiffAt_const))

variable {A} (hs : A.toLinearMap.IsSymmetric)
include hs

theorem inner_linEquiv_symm (x x' : E) :
    ⟪(linEquiv hs).symm x, x'⟫ = ⟪x, (linEquiv hs).symm x'⟫ := by
  have hx : kerProj A ((linEquiv hs).symm x) + A ((linEquiv hs).symm x) = x := by
    rw [← linEquiv_apply hs, ContinuousLinearEquiv.apply_symm_apply]
  have hx' : kerProj A ((linEquiv hs).symm x') + A ((linEquiv hs).symm x') = x' := by
    rw [← linEquiv_apply hs, ContinuousLinearEquiv.apply_symm_apply]
  have hA : ⟪A ((linEquiv hs).symm x), (linEquiv hs).symm x'⟫ =
      ⟪(linEquiv hs).symm x, A ((linEquiv hs).symm x')⟫ := hs _ _
  calc ⟪(linEquiv hs).symm x, x'⟫
      = ⟪(linEquiv hs).symm x,
          kerProj A ((linEquiv hs).symm x') + A ((linEquiv hs).symm x')⟫ := by rw [hx']
    _ = ⟪kerProj A ((linEquiv hs).symm x) + A ((linEquiv hs).symm x),
          (linEquiv hs).symm x'⟫ := by
        rw [inner_add_right, inner_add_left, inner_kerProj, hA]
    _ = ⟪x, (linEquiv hs).symm x'⟫ := by rw [hx]

theorem adjL_linEquiv_symm :
    adjL ((linEquiv hs).symm : E →L[ℝ] E) = ((linEquiv hs).symm : E →L[ℝ] E) :=
  ContinuousLinearMap.ext fun y => ext_inner_right ℝ fun z => by
    rw [adjL_inner_left]
    exact (inner_linEquiv_symm hs y z).symm

/-- The symmetrization of `(P + A)⁻¹` is `(P + A)⁻¹`. -/
theorem sym_linEquiv_symm :
    sym A ((linEquiv hs).symm : E →L[ℝ] E) = ((linEquiv hs).symm : E →L[ℝ] E) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [sym_apply, adjL_linEquiv_symm hs]
  have h1 : (1 / 2 : ℝ) • (((linEquiv hs).symm : E →L[ℝ] E) (cokerProj A x) +
      ((linEquiv hs).symm : E →L[ℝ] E) (cokerProj A x)) =
      (linEquiv hs).symm (cokerProj A x) := by
    rw [← two_smul ℝ, smul_smul]
    norm_num
  have h2 : cokerProj A ((linEquiv hs).symm (cokerProj A x)) =
      (linEquiv hs).symm (cokerProj A x) := by
    rw [cokerProj_apply, kerProj_linEquiv_symm hs, kerProj_cokerProj, sub_zero]
  have h3 : (linEquiv hs).symm (kerProj A x) = kerProj A x :=
    linEquiv_symm_of_map_eq_zero hs (map_kerProj A x)
  rw [h1, h2]
  calc kerProj A x + (linEquiv hs).symm (cokerProj A x)
      = (linEquiv hs).symm (kerProj A x) + (linEquiv hs).symm (cokerProj A x) := by rw [h3]
    _ = (linEquiv hs).symm (kerProj A x + cokerProj A x) := (map_add _ _ _).symm
    _ = (linEquiv hs).symm x := by rw [kerProj_add_cokerProj]

end Linear

/-! ### The reduced function along segments towards the kernel -/

section Reduced

variable {A : E →L[ℝ] E} {G : E → E} {p : E} {f : E → ℝ} {σ : E → E}

/-- Near `0` the function `w ↦ f (p + σ w)` is differentiable, the derivative of `σ` does not
change the kernel component, and on transverse directions `G (p + σ w)` pairs like `Q w`. -/
theorem eventually_reduced_deriv
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hσ : ContDiffAt ℝ 2 σ 0) (hσ0 : σ 0 = 0)
    (hr : ∀ᶠ w in 𝓝 (0 : E), kerProj A (σ w) = kerProj A w ∧
      cokerProj A (G (p + σ w)) = cokerProj A w) :
    ∀ᶠ w in 𝓝 (0 : E),
      HasFDerivAt (fun w => f (p + σ w)) ((innerSL ℝ (G (p + σ w))).comp (fderiv ℝ σ w)) w ∧
      (kerProj A).comp (fderiv ℝ σ w) = kerProj A ∧
      ∀ η, ⟪G (p + σ w), fderiv ℝ σ w (cokerProj A η)⟫ =
        ⟪cokerProj A w, fderiv ℝ σ w (cokerProj A η)⟫ := by
  have h1 : ContDiffAt ℝ 1 σ 0 := hσ.of_le (by norm_num)
  have hdiff : ∀ᶠ w in 𝓝 (0 : E), DifferentiableAt ℝ σ w :=
    (h1.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have htend : Tendsto (fun w => p + σ w) (𝓝 (0 : E)) (𝓝 p) := by
    have h : ContinuousAt (fun w => p + σ w) 0 := continuousAt_const.add hσ.continuousAt
    have h' := h.tendsto
    rwa [hσ0, add_zero] at h'
  have hfσ : ∀ᶠ w in 𝓝 (0 : E), HasFDerivAt f (innerSL ℝ (G (p + σ w))) (p + σ w) :=
    htend.eventually hf
  filter_upwards [hdiff, hfσ, hr.eventually_nhds] with w hdw hfw hrw
  have hσw : HasFDerivAt σ (fderiv ℝ σ w) w := hdw.hasFDerivAt
  have hproj : (kerProj A).comp (fderiv ℝ σ w) = kerProj A := by
    have ha : HasFDerivAt (fun w => kerProj A (σ w)) ((kerProj A).comp (fderiv ℝ σ w)) w :=
      (kerProj A).hasFDerivAt.comp w hσw
    have hb : HasFDerivAt (fun w => kerProj A (σ w)) (kerProj A) w :=
      (kerProj A).hasFDerivAt.congr_of_eventuallyEq (hrw.mono fun y hy => hy.1)
    exact ha.unique hb
  refine ⟨hfw.comp w (hσw.const_add p), hproj, fun η => ?_⟩
  have hG' : kerProj A (G (p + σ w)) + cokerProj A w = G (p + σ w) := by
    rw [← hrw.self_of_nhds.2, kerProj_add_cokerProj]
  have hη : kerProj A (fderiv ℝ σ w (cokerProj A η)) = 0 :=
    (congrArg (fun L : E →L[ℝ] E => L (cokerProj A η)) hproj).trans (kerProj_cokerProj A η)
  calc ⟪G (p + σ w), fderiv ℝ σ w (cokerProj A η)⟫
      = ⟪kerProj A (G (p + σ w)) + cokerProj A w, fderiv ℝ σ w (cokerProj A η)⟫ := by
        rw [hG']
    _ = ⟪cokerProj A w, fderiv ℝ σ w (cokerProj A η)⟫ := by
        rw [inner_add_left, inner_kerProj, hη, inner_zero_right, zero_add]

/-- Integration along the segment from `P w` to `w`: the difference of the reduced function is
the quadratic form of the averaged derivative of the reduction map on the transverse part. -/
theorem eventually_reduced_sub
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hσ : ContDiffAt ℝ 2 σ 0) (hσ0 : σ 0 = 0)
    (hr : ∀ᶠ w in 𝓝 (0 : E), kerProj A (σ w) = kerProj A w ∧
      cokerProj A (G (p + σ w)) = cokerProj A w) :
    ∀ᶠ w in 𝓝 (0 : E), f (p + σ w) - f (p + σ (kerProj A w)) =
      ⟪cokerProj A w, avg (fderiv ℝ σ) (kerProj A) (cokerProj A) w (cokerProj A w)⟫ := by
  have hDσ : ContDiffAt ℝ 1 (fderiv ℝ σ) 0 := hσ.fderiv_right (by norm_num)
  have hcont : ∀ᶠ x in 𝓝 (0 : E), ContinuousAt (fderiv ℝ σ) x :=
    (hDσ.eventually (by simp)).mono fun x hx => hx.continuousAt
  have hseg := eventually_segment ((eventually_reduced_deriv hf hσ hσ0 hr).and hcont)
    (kerProj A) (cokerProj A)
  filter_upwards [hseg] with w hw
  -- the functional `T ↦ ⟪Q w, T (Q w)⟫`
  set ev : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (innerSL ℝ (cokerProj A w)).comp (ContinuousLinearMap.apply ℝ E (cokerProj A w)) with hev
  have hev_apply : ∀ T : E →L[ℝ] E, ev T = ⟪cokerProj A w, T (cokerProj A w)⟫ := fun T => rfl
  have hφ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (p + σ (kerProj A w + s • cokerProj A w)))
        (ev (t • fderiv ℝ σ (kerProj A w + t • cokerProj A w))) t := by
    intro t ht
    obtain ⟨⟨hd, -, hη⟩, -⟩ := hw t ht
    have h := hasDerivAt_segment (φ := fun w => f (p + σ w)) (P := kerProj A)
      (Q := cokerProj A) (w := w) (t := t) hd
    refine h.congr_deriv ?_
    have hQ : cokerProj A (kerProj A w + t • cokerProj A w) = t • cokerProj A w := by
      rw [map_add, map_smul, cokerProj_kerProj, cokerProj_cokerProj, zero_add]
    change ⟪G (p + σ (kerProj A w + t • cokerProj A w)),
      fderiv ℝ σ (kerProj A w + t • cokerProj A w) (cokerProj A w)⟫ = _
    rw [hη w, hQ, hev_apply, smul_apply, real_inner_smul_left,
      real_inner_smul_right]
  have hg : ContinuousOn
      (fun t : ℝ => ev (t • fderiv ℝ σ (kerProj A w + t • cokerProj A w))) (Icc 0 1) := by
    intro t ht
    have hline : ContinuousAt (fun s : ℝ => kerProj A w + s • cokerProj A w) t := by fun_prop
    have h1 : ContinuousAt (fun s : ℝ => fderiv ℝ σ (kerProj A w + s • cokerProj A w)) t :=
      ContinuousAt.comp (f := fun s : ℝ => kerProj A w + s • cokerProj A w) (x := t)
        (hw t ht).2 hline
    exact (ev.continuous.continuousAt.comp (continuousAt_id.smul h1)).continuousWithinAt
  have hint := integrable_avg (L := fderiv ℝ σ) (P := kerProj A) (Q := cokerProj A) (w := w)
    (fun t ht => (hw t ht).2)
  calc f (p + σ w) - f (p + σ (kerProj A w))
      = ∫ t in (0 : ℝ)..1, ev (t • fderiv ℝ σ (kerProj A w + t • cokerProj A w)) :=
        sub_eq_integral (φ := fun w => f (p + σ w)) (kerProj_add_cokerProj A) hφ hg
    _ = ∫ t : Icc (0 : ℝ) 1,
          ev ((t : ℝ) • fderiv ℝ σ (kerProj A w + (t : ℝ) • cokerProj A w)) ∂unitMeasure :=
        (integral_unit fun t : ℝ =>
          ev (t • fderiv ℝ σ (kerProj A w + t • cokerProj A w))).symm
    _ = ev (avg (fderiv ℝ σ) (kerProj A) (cokerProj A) w) :=
        ContinuousLinearMap.integral_comp_comm ev hint
    _ = ⟪cokerProj A w, avg (fderiv ℝ σ) (kerProj A) (cokerProj A) w (cokerProj A w)⟫ :=
        hev_apply _

end Reduced

/-! ### The splitting chart -/

section Chart

variable {A : E →L[ℝ] E} (hs : A.toLinearMap.IsSymmetric) {G : E → E} {p : E} {f : E → ℝ}
  {σ : E → E}

include hs in
/-- The splitting chart for a given reduction map. -/
theorem exists_chart (hG : ContDiffAt ℝ 2 G p) (hA : HasFDerivAt G A p) (hp : G p = 0)
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hσ : ContDiffAt ℝ 2 σ 0) (hσ0 : σ 0 = 0)
    (hσd : HasStrictFDerivAt σ ((linEquiv hs).symm : E →L[ℝ] E) 0)
    (hr : ∀ᶠ w in 𝓝 (0 : E), kerProj A (σ w) = kerProj A w ∧
      cokerProj A (G (p + σ w)) = cokerProj A w)
    (hl : ∀ᶠ z in 𝓝 (0 : E), σ (kerProj A z + cokerProj A (G (p + z))) = z) :
    ∃ Ξ : E → E, ContDiffAt ℝ 1 Ξ 0 ∧ Ξ 0 = 0 ∧
      HasStrictFDerivAt Ξ (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ᶠ z in 𝓝 (0 : E), kerProj A (Ξ z) = kerProj A z) ∧
      ∀ᶠ z in 𝓝 (0 : E),
        f (p + z) = f (p + σ (kerProj A z)) + 1 / 2 * ⟪A (Ξ z), Ξ z⟫ := by
  -- the averaged derivative of the reduction map
  have hDσ : ContDiffAt ℝ 1 (fderiv ℝ σ) 0 := hσ.fderiv_right (by norm_num)
  have hB1 : ContDiffAt ℝ 1 (avg (fderiv ℝ σ) (kerProj A) (cokerProj A)) 0 := by
    have h := avg_contDiffAt (n := 1) (L := fderiv ℝ σ) (by exact_mod_cast hDσ)
      (kerProj A) (cokerProj A)
    exact_mod_cast h
  have hB0 : avg (fderiv ℝ σ) (kerProj A) (cokerProj A) 0 =
      (1 / 2 : ℝ) • ((linEquiv hs).symm : E →L[ℝ] E) := by
    rw [avg_zero, hσd.hasFDerivAt.fderiv]
  -- the symmetric family and its congruence
  have hS1 : ContDiffAt ℝ 1
      (fun w => sym A ((2 : ℝ) • avg (fderiv ℝ σ) (kerProj A) (cokerProj A) w)) 0 :=
    sym_contDiffAt A (hB1.const_smul (2 : ℝ))
  have hS0 : ((linEquiv hs).symm : E →L[ℝ] E) =
      sym A ((2 : ℝ) • avg (fderiv ℝ σ) (kerProj A) (cokerProj A) 0) := by
    rw [hB0, smul_smul]
    norm_num
    exact (sym_linEquiv_symm hs).symm
  obtain ⟨R, hR1, hR0, hcong, hJ⟩ := exists_congruence hS1
    (Eventually.of_forall fun w x x' => inner_sym A _ x x') (linEquiv hs).symm hS0
  have hcomm := hJ (reflEquiv A) (Eventually.of_forall fun w x => sym_refl A _ x)
  have hsub := eventually_reduced_sub (A := A) hf hσ hσ0 hr
  -- the statement in the coordinates of the reduction map
  have hw : ∀ᶠ w in 𝓝 (0 : E),
      kerProj A (kerProj A w + (linEquiv hs).symm (R w (cokerProj A w))) = kerProj A w ∧
      f (p + σ w) = f (p + σ (kerProj A w)) +
        1 / 2 * ⟪A (kerProj A w + (linEquiv hs).symm (R w (cokerProj A w))),
          kerProj A w + (linEquiv hs).symm (R w (cokerProj A w))⟫ := by
    filter_upwards [hsub, hcong, hcomm] with w h1 h2 h3
    obtain ⟨u, hu⟩ : ∃ u, u = R w (cokerProj A w) := ⟨_, rfl⟩
    obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = (linEquiv hs).symm u := ⟨_, rfl⟩
    rw [← hu, ← hξ]
    have hPu : kerProj A u = 0 := by
      have h := h3 (cokerProj A w)
      have hre : reflEquiv A (cokerProj A w) = -cokerProj A w := by
        rw [reflEquiv_apply, kerProj_cokerProj, cokerProj_cokerProj, zero_sub]
      rw [hre, map_neg, ← hu, reflEquiv_apply] at h
      have hsum := kerProj_add_cokerProj A u
      have h2u : kerProj A u + kerProj A u = 0 := by
        calc kerProj A u + kerProj A u
            = (kerProj A u - cokerProj A u) + (kerProj A u + cokerProj A u) := by abel
          _ = -u + u := by rw [← h, hsum]
          _ = 0 := neg_add_cancel u
      have h2' : (2 : ℝ) • kerProj A u = 0 := by
        rw [two_smul]
        exact h2u
      exact (smul_eq_zero.mp h2').resolve_left two_ne_zero
    have hPξ : kerProj A ξ = 0 := by rw [hξ, kerProj_linEquiv_symm hs, hPu]
    have hAξ : A ξ = u := by
      have h := (linEquiv hs).apply_symm_apply u
      rw [← hξ, linEquiv_apply hs, hPξ, zero_add] at h
      exact h
    refine ⟨by rw [map_add, kerProj_kerProj, hPξ, add_zero], ?_⟩
    have hquad : 2 * ⟪cokerProj A w,
        avg (fderiv ℝ σ) (kerProj A) (cokerProj A) w (cokerProj A w)⟫ = ⟪ξ, A ξ⟫ := by
      have e2 := h2 (cokerProj A w) (cokerProj A w)
      rw [← hu, ← hξ, inner_sym_cokerProj, smul_apply, real_inner_smul_left,
        ← hAξ] at e2
      rw [real_inner_comm (cokerProj A w)] at e2
      linarith
    have hinner : ⟪A (kerProj A w + ξ), kerProj A w + ξ⟫ = ⟪ξ, A ξ⟫ := by
      have h0 : ⟪A ξ, kerProj A w⟫ = 0 := by
        have h : ⟪A ξ, kerProj A w⟫ = ⟪ξ, A (kerProj A w)⟫ := hs ξ (kerProj A w)
        rw [h, map_kerProj, inner_zero_right]
      rw [map_add, map_kerProj, zero_add, inner_add_right, h0, zero_add, real_inner_comm]
    rw [hinner, ← hquad]
    linarith
  -- the chart
  have hΨ1 : ContDiffAt ℝ 1 (aux G p A) 0 := (aux_contDiffAt hG).of_le (by norm_num)
  have hΨ0 : aux G p A 0 = 0 := aux_zero hp
  have hΨd : HasFDerivAt (aux G p A) (linEquiv hs : E →L[ℝ] E) 0 := aux_hasFDerivAt hs hA
  have hΨt : Tendsto (aux G p A) (𝓝 (0 : E)) (𝓝 0) := by
    have h := hΨ1.continuousAt.tendsto
    rwa [hΨ0] at h
  have hPΨ : ∀ z, kerProj A (aux G p A z) = kerProj A z := fun z => by
    rw [aux, map_add, kerProj_kerProj, kerProj_cokerProj, add_zero]
  have hθ1 : ContDiffAt ℝ 1
      (fun w => kerProj A w + (linEquiv hs).symm (R w (cokerProj A w))) 0 :=
    (kerProj A).contDiff.contDiffAt.add
      (((linEquiv hs).symm : E →L[ℝ] E).contDiff.contDiffAt.comp 0
        (hR1.clm_apply (cokerProj A).contDiff.contDiffAt))
  have hθd : HasFDerivAt (fun w => kerProj A w + (linEquiv hs).symm (R w (cokerProj A w)))
      ((linEquiv hs).symm : E →L[ℝ] E) 0 := by
    have h1 : HasFDerivAt R (fderiv ℝ R 0) 0 :=
      (hR1.differentiableAt (by norm_num)).hasFDerivAt
    have h3 := h1.clm_apply (cokerProj A).hasFDerivAt
    have h4 := ((linEquiv hs).symm : E →L[ℝ] E).hasFDerivAt.comp (0 : E) h3
    have h5 := (kerProj A).hasFDerivAt.add h4
    have he : kerProj A + ((linEquiv hs).symm : E →L[ℝ] E).comp
        ((R 0).comp (cokerProj A) + (fderiv ℝ R 0).flip (cokerProj A 0)) =
        ((linEquiv hs).symm : E →L[ℝ] E) := by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [hR0, map_zero, map_zero, add_zero]
      change kerProj A x + (linEquiv hs).symm (cokerProj A x) = (linEquiv hs).symm x
      calc kerProj A x + (linEquiv hs).symm (cokerProj A x)
          = (linEquiv hs).symm (kerProj A x) + (linEquiv hs).symm (cokerProj A x) := by
            rw [linEquiv_symm_of_map_eq_zero hs (map_kerProj A x)]
        _ = (linEquiv hs).symm (kerProj A x + cokerProj A x) := (map_add _ _ _).symm
        _ = (linEquiv hs).symm x := by rw [kerProj_add_cokerProj]
    rw [he] at h5
    exact h5
  have hΞ1 : ContDiffAt ℝ 1 (fun z => kerProj A (aux G p A z) +
      (linEquiv hs).symm (R (aux G p A z) (cokerProj A (aux G p A z)))) 0 := by
    have h : ContDiffAt ℝ 1
        (fun w => kerProj A w + (linEquiv hs).symm (R w (cokerProj A w))) (aux G p A 0) := by
      rw [hΨ0]
      exact hθ1
    exact h.comp 0 hΨ1
  refine ⟨fun z => kerProj A (aux G p A z) +
    (linEquiv hs).symm (R (aux G p A z) (cokerProj A (aux G p A z))), hΞ1, ?_, ?_, ?_, ?_⟩
  · change kerProj A (aux G p A 0) +
      (linEquiv hs).symm (R (aux G p A 0) (cokerProj A (aux G p A 0))) = 0
    rw [hΨ0]
    simp
  · have hθd' : HasFDerivAt (fun w => kerProj A w + (linEquiv hs).symm (R w (cokerProj A w)))
        ((linEquiv hs).symm : E →L[ℝ] E) (aux G p A 0) := by
      rw [hΨ0]
      exact hθd
    have h := hθd'.comp (0 : E) hΨd
    have he : ((linEquiv hs).symm : E →L[ℝ] E).comp (linEquiv hs : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E :=
      ContinuousLinearMap.ext fun x => (linEquiv hs).symm_apply_apply x
    rw [he] at h
    exact hΞ1.hasStrictFDerivAt' h (by norm_num)
  · filter_upwards [hΨt.eventually hw] with z hz
    rw [hz.1, hPΨ]
  · filter_upwards [hΨt.eventually hw, hl] with z hz hlz
    have h := hz.2
    have hσΨ : σ (aux G p A z) = z := hlz
    have e : f (p + σ (kerProj A (aux G p A z))) = f (p + σ (kerProj A z)) := by rw [hPΨ]
    rw [hσΨ, e] at h
    exact h

include hs in
/-- **The degenerate splitting lemma.** There are a reduction map `σ` and a chart `Ξ`, tangent
to the identity at `0` and preserving the kernel coordinate, in which `f (p + z)` is the sum of
the reduced function `f (p + σ (P z))` of the kernel coordinate and the quadratic form of `A`. -/
theorem exists_splitting (hG : ContDiffAt ℝ 2 G p) (hA : HasFDerivAt G A p) (hp : G p = 0)
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x) :
    ∃ σ Ξ : E → E, ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0 : E), A w = 0 → kerProj A (σ w) = w ∧ A (G (p + σ w)) = 0) ∧
      (∀ᶠ z in 𝓝 (0 : E), A (G (p + z)) = 0 → σ (kerProj A z) = z) ∧
      (∀ᶠ w in 𝓝 (0 : E), A w = 0 →
        HasFDerivAt (fun w => f (p + σ w))
          ((innerSL ℝ (G (p + σ w))).comp (kerProj A)) w) ∧
      ContDiffAt ℝ 1 Ξ 0 ∧ Ξ 0 = 0 ∧
      HasStrictFDerivAt Ξ (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ᶠ z in 𝓝 (0 : E), kerProj A (Ξ z) = kerProj A z) ∧
      ∀ᶠ z in 𝓝 (0 : E),
        f (p + z) = f (p + σ (kerProj A z)) + 1 / 2 * ⟪A (Ξ z), Ξ z⟫ := by
  obtain ⟨σ, hσ, hσ0, hσd, hr, hl⟩ :=
    exists_reduction hs (k := 2) (by norm_num) hG hA hp
  obtain ⟨Ξ, hΞ1, hΞ0, hΞd, hΞP, hΞf⟩ := exists_chart hs hG hA hp hf hσ hσ0 hσd hr hl
  refine ⟨σ, Ξ, hσ, hσ0, ?_, ?_, ?_, hΞ1, hΞ0, hΞd, hΞP, hΞf⟩
  · filter_upwards [hr] with w hw hAw
    refine ⟨by rw [hw.1, kerProj_of_map_eq_zero A hAw], ?_⟩
    refine map_eq_zero_of_cokerProj A ?_
    rw [hw.2, cokerProj_of_map_eq_zero A hAw]
  · filter_upwards [hl] with z hz hAz
    rw [cokerProj_of_map_eq_zero A hAz, add_zero] at hz
    exact hz
  · filter_upwards [eventually_reduced_deriv hf hσ hσ0 hr, hr] with w hw hrw hAw
    obtain ⟨hd, hproj, -⟩ := hw
    have hker : kerProj A (G (p + σ w)) = G (p + σ w) := by
      have h := hrw.2
      rw [cokerProj_of_map_eq_zero A hAw] at h
      exact (sub_eq_zero.mp h).symm
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
    rwa [heq] at hd

include hs in
/-- **The Morse lemma for a function with `C²` gradient.** If the symmetric derivative `A` of
the gradient at a critical point is injective, there is a chart `Ξ`, `C¹` at `0` and tangent to
the identity, in which `f (p + z) = f p + ⟪A (Ξ z), Ξ z⟫ / 2`. -/
theorem exists_morse (hG : ContDiffAt ℝ 2 G p) (hA : HasFDerivAt G A p) (hp : G p = 0)
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x) (hinj : ∀ w, A w = 0 → w = 0) :
    ∃ Ξ : E → E, ContDiffAt ℝ 1 Ξ 0 ∧ Ξ 0 = 0 ∧
      HasStrictFDerivAt Ξ (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ᶠ z in 𝓝 (0 : E), f (p + z) = f p + 1 / 2 * ⟪A (Ξ z), Ξ z⟫ := by
  obtain ⟨σ, Ξ, -, hσ0, -, -, -, hΞ1, hΞ0, hΞd, -, hΞf⟩ := exists_splitting hs hG hA hp hf
  refine ⟨Ξ, hΞ1, hΞ0, hΞd, hΞf.mono fun z hz => ?_⟩
  have hP : kerProj A z = 0 := hinj _ (map_kerProj A z)
  rw [hP, hσ0, add_zero] at hz
  exact hz

include hs in
/-- The splitting as a local homeomorphism: an open partial homeomorphism `e` fixing `0`, on
whose source the kernel coordinate is preserved and the function is the sum of the reduced
function and the quadratic form of `A`. -/
theorem exists_homeomorph (hG : ContDiffAt ℝ 2 G p) (hA : HasFDerivAt G A p) (hp : G p = 0)
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x) :
    ∃ (σ : E → E) (e : OpenPartialHomeomorph E E), ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      ∀ z ∈ e.source, kerProj A (e z) = kerProj A z ∧
        f (p + z) = f (p + σ (kerProj A z)) + 1 / 2 * ⟪A (e z), e z⟫ := by
  obtain ⟨σ, Ξ, hσ, hσ0, -, -, -, -, hΞ0, hΞd, hΞP, hΞf⟩ := exists_splitting hs hG hA hp hf
  obtain ⟨s, hs', hsopen, h0s⟩ := eventually_nhds_iff.mp (hΞP.and hΞf)
  have hd : HasStrictFDerivAt Ξ
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := hΞd
  refine ⟨σ, (hd.toOpenPartialHomeomorph Ξ).restrOpen s hsopen, hσ, hσ0, ?_, hΞ0, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hd.mem_toOpenPartialHomeomorph_source, h0s⟩
  · intro z hz
    rw [OpenPartialHomeomorph.restrOpen_source] at hz
    exact hs' z hz.2

end Chart

end

end Finsler.SplittingLemma
