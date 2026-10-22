module

public import Finsler.Analysis.LyapunovSchmidt

/-! Naturality of the reduction to the kernel under a linear map that intertwines two maps with
symmetric derivative up to a nonzero factor. Let `G₀` on `E₀` and `G` on `E` have zeros `p₀`,
`p` with symmetric derivatives `A₀`, `A`, and let `ι : E₀ → E` be continuous linear with
`G (p + ι z) = c • ι (G₀ (p₀ + z))` near `0`, `c ≠ 0`. Then `A ι = c • ι A₀`, the kernel and
cokernel projections commute with `ι`, and reduction maps `σ₀`, `σ` satisfy
`σ (ι (P₀ w + c • Q₀ w)) = ι (σ₀ w)` near `0`; on the kernel of `A₀` this is `σ (ι w) = ι (σ₀ w)`.
If `f (p + ι z) = d * f₀ (p₀ + z)` near `0`, the reduced functions satisfy
`f (p + σ (ι w)) = d * f₀ (p₀ + σ₀ w)` on the kernel of `A₀` near `0`. If moreover `ι` is
injective and the nullity of `A` is at most that of `A₀`, every kernel vector of `A` is the image
of a kernel vector of `A₀`, so the reduced function of `f` is determined by that of `f₀`.

The case `E₀ = E`, `c = 1` of an isometry fixing `p` gives the equivariance of the reduction
map; the case of the iteration map of closed polygons, with the factor coming from the scaling
of the energy, gives the comparison of the reduced functions of a closed geodesic and of its
iterates when the nullities agree (Gromoll and Meyer). The intertwining relation is derived from
a scaled isometry `ι` with `f ∘ ι = d f₀` whose image contains the gradients at its points
(symmetric criticality). No statement on local cohomology is made. -/

@[expose] public section

namespace Finsler.ReductionNaturality

open Filter Module Finsler.LyapunovSchmidt
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section

variable {E₀ E : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
  [FiniteDimensional ℝ E₀] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ### Linear part -/

section Linear

variable {A₀ : E₀ →L[ℝ] E₀} {A : E →L[ℝ] E} (hs₀ : A₀.toLinearMap.IsSymmetric)
  (hs : A.toLinearMap.IsSymmetric) {ι : E₀ →L[ℝ] E} {c : ℝ} (hc : c ≠ 0)
  (hA : ∀ v, A (ι v) = c • ι (A₀ v))

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
include hA in
/-- The image of a kernel vector is a kernel vector. -/
theorem map_of_map_eq_zero {v : E₀} (hv : A₀ v = 0) : A (ι v) = 0 := by
  rw [hA, hv, map_zero, smul_zero]

include hs₀ hs hc hA in
/-- The kernel projections commute with the intertwining map. -/
theorem kerProj_map (v : E₀) : kerProj A (ι v) = ι (kerProj A₀ v) := by
  have h1 : kerProj A (ι (kerProj A₀ v)) = ι (kerProj A₀ v) :=
    kerProj_of_map_eq_zero A (map_of_map_eq_zero hA (map_kerProj A₀ v))
  have h2 : kerProj A (ι (cokerProj A₀ v)) = 0 := by
    have h3 : ι (cokerProj A₀ v) = c⁻¹ • A (ι ((linEquiv hs₀).symm v)) := by
      rw [hA, map_linEquiv_symm hs₀, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h3, map_smul, LyapunovSchmidt.kerProj_map hs, smul_zero]
  calc kerProj A (ι v) = kerProj A (ι (kerProj A₀ v + cokerProj A₀ v)) := by
        rw [kerProj_add_cokerProj]
    _ = kerProj A (ι (kerProj A₀ v)) + kerProj A (ι (cokerProj A₀ v)) := by
        rw [map_add, map_add]
    _ = ι (kerProj A₀ v) := by rw [h1, h2, add_zero]

include hs₀ hs hc hA in
/-- The complementary projections commute with the intertwining map. -/
theorem cokerProj_map (v : E₀) : cokerProj A (ι v) = ι (cokerProj A₀ v) := by
  rw [cokerProj_apply, cokerProj_apply, kerProj_map hs₀ hs hc hA, map_sub]

omit [FiniteDimensional ℝ E₀] in
include hA in
/-- An injective intertwining map does not decrease the nullity. -/
theorem finrank_ker_le (hinj : Function.Injective ι) :
    finrank ℝ (LinearMap.ker A₀.toLinearMap) ≤ finrank ℝ (LinearMap.ker A.toLinearMap) := by
  set φ : LinearMap.ker A₀.toLinearMap →ₗ[ℝ] LinearMap.ker A.toLinearMap :=
    ι.toLinearMap.restrict fun v hv =>
      LinearMap.mem_ker.mpr (map_of_map_eq_zero hA (LinearMap.mem_ker.mp hv)) with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))
  exact LinearMap.finrank_le_finrank_of_injective hφinj

include hA in
/-- If the intertwining map is injective and the nullity of `A` is at most that of `A₀`, every
kernel vector of `A` is the image of a kernel vector of `A₀`. -/
theorem exists_of_finrank_le (hinj : Function.Injective ι)
    (hfin : finrank ℝ (LinearMap.ker A.toLinearMap) ≤ finrank ℝ (LinearMap.ker A₀.toLinearMap))
    {k : E} (hk : A k = 0) : ∃ w, A₀ w = 0 ∧ ι w = k := by
  set φ : LinearMap.ker A₀.toLinearMap →ₗ[ℝ] LinearMap.ker A.toLinearMap :=
    ι.toLinearMap.restrict fun v hv =>
      LinearMap.mem_ker.mpr (map_of_map_eq_zero hA (LinearMap.mem_ker.mp hv)) with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (le_antisymm (finrank_ker_le hA hinj) hfin)).mp hφinj
  obtain ⟨w, hw⟩ := hφsurj ⟨k, LinearMap.mem_ker.mpr hk⟩
  exact ⟨w, LinearMap.mem_ker.mp w.2, congrArg Subtype.val hw⟩

end Linear

/-! ### The intertwining relation from symmetric criticality -/

section Criticality

variable {ι : E₀ →L[ℝ] E} {κ d : ℝ} {f₀ : E₀ → ℝ} {f : E → ℝ} {G₀ : E₀ → E₀} {G : E → E}
  {x : E₀}

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
/-- Symmetric criticality. Let `ι` multiply inner products by `κ ≠ 0`, let `f ∘ ι = d f₀` near
`x`, and let `G₀`, `G` represent the derivatives of `f₀` at `x` and of `f` at `ι x`. If
`G (ι x)` lies in the image of `ι`, then `G (ι x) = (d / κ) • ι (G₀ x)`. -/
theorem gradient_map (hκ : κ ≠ 0) (hι : ∀ u v, ⟪ι u, ι v⟫ = κ * ⟪u, v⟫)
    (hff : ∀ᶠ y in 𝓝 x, f (ι y) = d * f₀ y)
    (hf₀ : HasFDerivAt f₀ (innerSL ℝ (G₀ x)) x) (hf : HasFDerivAt f (innerSL ℝ (G (ι x))) (ι x))
    (hmem : ∃ u, ι u = G (ι x)) : G (ι x) = (d / κ) • ι (G₀ x) := by
  obtain ⟨u, hu⟩ := hmem
  have h1 : HasFDerivAt (fun y => f (ι y)) ((innerSL ℝ (G (ι x))).comp ι) x :=
    hf.comp x ι.hasFDerivAt
  have h2 : HasFDerivAt (fun y => f (ι y)) (d • innerSL ℝ (G₀ x)) x :=
    (hf₀.const_mul d).congr_of_eventuallyEq hff
  have h3 := h1.unique h2
  have h4 : ∀ v, κ * ⟪u, v⟫ = d * ⟪G₀ x, v⟫ := fun v => by
    have h := congrArg (fun L : E₀ →L[ℝ] ℝ => L v) h3
    have h' : ⟪G (ι x), ι v⟫ = d * ⟪G₀ x, v⟫ := h
    rw [← hu, hι] at h'
    exact h'
  have h5 : u = (d / κ) • G₀ x := by
    refine ext_inner_right ℝ fun v => ?_
    rw [real_inner_smul_left]
    have h := h4 v
    field_simp
    linarith
  rw [← hu, h5, map_smul]

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
/-- The gradient at a fixed point of a linear map that preserves inner products and the function
is fixed by that map. -/
theorem gradient_fixed {ρ : E →L[ℝ] E} (hρ : ∀ u v, ⟪ρ u, ρ v⟫ = ⟪u, v⟫) {f : E → ℝ}
    {G : E → E} {y : E} (hy : ρ y = y) (hfρ : ∀ᶠ z in 𝓝 y, f (ρ z) = f z)
    (hf : HasFDerivAt f (innerSL ℝ (G y)) y) : ρ (G y) = G y := by
  have hf' : HasFDerivAt f (innerSL ℝ (G y)) (ρ y) := by rwa [hy]
  have h1 : HasFDerivAt (fun z => f (ρ z)) ((innerSL ℝ (G y)).comp ρ) y :=
    hf'.comp y ρ.hasFDerivAt
  have h2 : HasFDerivAt (fun z => f (ρ z)) (innerSL ℝ (G y)) y :=
    hf.congr_of_eventuallyEq hfρ
  have h3 := h1.unique h2
  have h4 : ∀ v, ⟪G y, ρ v⟫ = ⟪G y, v⟫ := fun v =>
    congrArg (fun L : E →L[ℝ] ℝ => L v) h3
  have h5 : ⟪ρ (G y) - G y, ρ (G y) - G y⟫ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hρ, h4 (G y),
      real_inner_comm (G y) (ρ (G y)), h4 (G y)]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h5)

end Criticality

/-! ### Reduction maps -/

section Reduction

variable {A₀ : E₀ →L[ℝ] E₀} {A : E →L[ℝ] E} (hs₀ : A₀.toLinearMap.IsSymmetric)
  (hs : A.toLinearMap.IsSymmetric) {ι : E₀ →L[ℝ] E} {c : ℝ} (hc : c ≠ 0)
  {G₀ : E₀ → E₀} {G : E → E} {p₀ : E₀} {p : E}

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
/-- The derivatives are intertwined if the maps are. -/
theorem map_deriv (hG₀ : HasFDerivAt G₀ A₀ p₀) (hG : HasFDerivAt G A p)
    (hι : ∀ᶠ z in 𝓝 (0 : E₀), G (p + ι z) = c • ι (G₀ (p₀ + z))) (v : E₀) :
    A (ι v) = c • ι (A₀ v) := by
  have hG' : HasFDerivAt G A (p + ι 0) := by rwa [map_zero, add_zero]
  have hG₀' : HasFDerivAt G₀ A₀ (p₀ + 0) := by rwa [add_zero]
  have h1 : HasFDerivAt (fun z : E₀ => G (p + ι z)) (A.comp ι) 0 :=
    hG'.comp (0 : E₀) (ι.hasFDerivAt.const_add p)
  have h2 : HasFDerivAt (fun z : E₀ => G₀ (p₀ + z)) A₀ 0 :=
    (hasFDerivAt_comp_add_left p₀).mpr hG₀'
  have h3 : HasFDerivAt (fun z : E₀ => c • ι (G₀ (p₀ + z))) (c • ι.comp A₀) 0 :=
    (ι.hasFDerivAt.comp (0 : E₀) h2).const_smul c
  have h4 := h1.unique (h3.congr_of_eventuallyEq hι)
  exact congrArg (fun L : E₀ →L[ℝ] E => L v) h4

include hs₀ hs hc in
/-- Reduction maps are intertwined. -/
theorem eventually_reduction_map (hA : ∀ v, A (ι v) = c • ι (A₀ v))
    (hι : ∀ᶠ z in 𝓝 (0 : E₀), G (p + ι z) = c • ι (G₀ (p₀ + z)))
    {σ₀ : E₀ → E₀} {σ : E → E} (hσ₀ : ContinuousAt σ₀ 0) (hσ₀0 : σ₀ 0 = 0)
    (hr₀ : ∀ᶠ w in 𝓝 (0 : E₀), kerProj A₀ (σ₀ w) = kerProj A₀ w ∧
      cokerProj A₀ (G₀ (p₀ + σ₀ w)) = cokerProj A₀ w)
    (hl : ∀ᶠ z in 𝓝 (0 : E), σ (kerProj A z + cokerProj A (G (p + z))) = z) :
    ∀ᶠ w in 𝓝 (0 : E₀), σ (ι (kerProj A₀ w + c • cokerProj A₀ w)) = ι (σ₀ w) := by
  have ht₀ : Tendsto σ₀ (𝓝 (0 : E₀)) (𝓝 0) := by
    have h := hσ₀.tendsto
    rwa [hσ₀0] at h
  have ht : Tendsto (fun w => ι (σ₀ w)) (𝓝 (0 : E₀)) (𝓝 0) := by
    have h := (ι.continuous.tendsto 0).comp ht₀
    rwa [map_zero] at h
  filter_upwards [hr₀, ht₀.eventually hι, ht.eventually hl] with w h1 h2 h3
  have e1 : kerProj A (ι (σ₀ w)) = ι (kerProj A₀ w) := by
    rw [kerProj_map hs₀ hs hc hA, h1.1]
  have e2 : cokerProj A (G (p + ι (σ₀ w))) = c • ι (cokerProj A₀ w) := by
    rw [h2, map_smul, cokerProj_map hs₀ hs hc hA, h1.2]
  rw [e1, e2] at h3
  rw [map_add, map_smul]
  exact h3

include hs₀ hs hc in
/-- On the kernel the reduction maps are intertwined by the intertwining map itself. -/
theorem eventually_reduction_map_ker (hA : ∀ v, A (ι v) = c • ι (A₀ v))
    (hι : ∀ᶠ z in 𝓝 (0 : E₀), G (p + ι z) = c • ι (G₀ (p₀ + z)))
    {σ₀ : E₀ → E₀} {σ : E → E} (hσ₀ : ContinuousAt σ₀ 0) (hσ₀0 : σ₀ 0 = 0)
    (hr₀ : ∀ᶠ w in 𝓝 (0 : E₀), kerProj A₀ (σ₀ w) = kerProj A₀ w ∧
      cokerProj A₀ (G₀ (p₀ + σ₀ w)) = cokerProj A₀ w)
    (hl : ∀ᶠ z in 𝓝 (0 : E), σ (kerProj A z + cokerProj A (G (p + z))) = z) :
    ∀ᶠ w in 𝓝 (0 : E₀), A₀ w = 0 → σ (ι w) = ι (σ₀ w) := by
  filter_upwards [eventually_reduction_map hs₀ hs hc hA hι hσ₀ hσ₀0 hr₀ hl] with w hw hAw
  rwa [kerProj_of_map_eq_zero A₀ hAw, cokerProj_of_map_eq_zero A₀ hAw, smul_zero, add_zero]
    at hw

include hs₀ hs hc in
/-- The reduced functions are intertwined on the kernel. -/
theorem eventually_reduced_map (hA : ∀ v, A (ι v) = c • ι (A₀ v))
    (hι : ∀ᶠ z in 𝓝 (0 : E₀), G (p + ι z) = c • ι (G₀ (p₀ + z)))
    {σ₀ : E₀ → E₀} {σ : E → E} (hσ₀ : ContinuousAt σ₀ 0) (hσ₀0 : σ₀ 0 = 0)
    (hr₀ : ∀ᶠ w in 𝓝 (0 : E₀), kerProj A₀ (σ₀ w) = kerProj A₀ w ∧
      cokerProj A₀ (G₀ (p₀ + σ₀ w)) = cokerProj A₀ w)
    (hl : ∀ᶠ z in 𝓝 (0 : E), σ (kerProj A z + cokerProj A (G (p + z))) = z)
    {f₀ : E₀ → ℝ} {f : E → ℝ} {d : ℝ}
    (hf : ∀ᶠ z in 𝓝 (0 : E₀), f (p + ι z) = d * f₀ (p₀ + z)) :
    ∀ᶠ w in 𝓝 (0 : E₀), A₀ w = 0 → f (p + σ (ι w)) = d * f₀ (p₀ + σ₀ w) := by
  have ht₀ : Tendsto σ₀ (𝓝 (0 : E₀)) (𝓝 0) := by
    have h := hσ₀.tendsto
    rwa [hσ₀0] at h
  filter_upwards [eventually_reduction_map_ker hs₀ hs hc hA hι hσ₀ hσ₀0 hr₀ hl,
    ht₀.eventually hf] with w h1 h2 hAw
  rw [h1 hAw, h2]

end Reduction

end

end Finsler.ReductionNaturality
