import SurfaceMorseData
import Finsler.Analysis.HessianSplitting

/-!
# From a symmetric splitting to a maximal disk

Spectral coordinates separate the nonpositive and positive directions of a
finite-dimensional symmetric Hessian. The reduced function only needs to
be checked on the kernel: its strict local maximum then extends over all
nonpositive directions. The positive directions supply the detector's
central minimum, so the small disk and its left inverse can be constructed.

This is a local lemma for a transverse slice when applying it to a closed
geodesic. A phase direction has constant energy and must first be removed;
strict maximality on the full kernel of every geodesic is not asserted.
-/

namespace Finsler.SurfaceSpectralDisk

open Set Filter Module
open Finsler.HessianSplitting Finsler.LyapunovSchmidt Finsler.SurfaceMorseData
open scoped Topology RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)

/-- The negative and zero spectral directions together. -/
def nonpositive : Submodule ℝ E :=
  hT.eigenvectorSpan rfl {i | hT.eigenvalues rfl i ≤ 0}

theorem repr_zero_of_not_mem {s : Set (Fin (finrank ℝ E))} {v : E}
    (hv : v ∈ hT.eigenvectorSpan rfl s) {i : Fin (finrank ℝ E)} (hi : i ∉ s) :
    (hT.eigenvectorBasis rfl).repr v i = 0 := by
  by_contra hc
  apply hi
  apply (hT.mem_eigenvectorSpan_iff rfl).mp hv
  exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by
    rwa [OrthonormalBasis.coe_toBasis_repr_apply]))

/-- Inner products in the ordered orthonormal eigenbasis. -/
theorem inner_eq_sum (v w : E) : ⟪v, w⟫ =
    ∑ i, (hT.eigenvectorBasis rfl).repr v i * (hT.eigenvectorBasis rfl).repr w i := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner v w]
  apply Finset.sum_congr rfl
  intro i hi
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    real_inner_comm v]

/-- The Hessian quadratic form is the eigenvalue-weighted sum of squares. -/
theorem quadratic_eq_sum (v : E) : ⟪T v, v⟫ =
    ∑ i, hT.eigenvalues rfl i * ((hT.eigenvectorBasis rfl).repr v i) ^ 2 := by
  rw [inner_eq_sum T hT]
  apply Finset.sum_congr rfl
  intro i hi
  rw [repr_apply T hT]
  ring

theorem spectral_inner_eq_zero {s t : Set (Fin (finrank ℝ E))}
    (hst : Disjoint s t) {v w : E}
    (hv : v ∈ hT.eigenvectorSpan rfl s) (hw : w ∈ hT.eigenvectorSpan rfl t) :
    ⟪v, w⟫ = 0 := by
  rw [inner_eq_sum T hT]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases his : i ∈ s
  · rw [repr_zero_of_not_mem T hT hw (fun hit => Set.disjoint_left.mp hst his hit), mul_zero]
  · rw [repr_zero_of_not_mem T hT hv his, zero_mul]

theorem nonpositive_eq : nonpositive T hT = negative T hT ⊔ LinearMap.ker T.toLinearMap := by
  rw [nonpositive, ← zeroSpace_eq_ker T hT, negative, zeroSpace, ← hT.eigenvectorSpan_union rfl]
  congr 1
  ext i
  change hT.eigenvalues rfl i ≤ 0 ↔ hT.eigenvalues rfl i < 0 ∨ hT.eigenvalues rfl i = 0
  exact le_iff_lt_or_eq

theorem nonpositive_isCompl_positive : IsCompl (nonpositive T hT) (positive T hT) := by
  refine ⟨hT.disjoint_eigenvectorSpan rfl (Set.disjoint_left.mpr ?_),
    codisjoint_iff.mpr ?_⟩
  · intro i hi hj
    exact (not_lt_of_ge (show hT.eigenvalues rfl i ≤ 0 from hi)) hj
  · rw [nonpositive, positive, ← hT.eigenvectorSpan_union rfl]
    have h : {i | hT.eigenvalues rfl i ≤ 0} ∪ {i | 0 < hT.eigenvalues rfl i} = univ := by
      ext i
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      exact le_or_gt _ _
    rw [h, hT.eigenvectorSpan_univ rfl]

theorem quadratic_nonpos {v : E} (hv : v ∈ nonpositive T hT) : ⟪T v, v⟫ ≤ 0 := by
  rw [quadratic_eq_sum T hT]
  apply Finset.sum_nonpos
  intro i hi
  by_cases hev : hT.eigenvalues rfl i ≤ 0
  · exact mul_nonpos_of_nonpos_of_nonneg hev (sq_nonneg _)
  · rw [repr_zero_of_not_mem T hT hv hev, zero_pow (by decide : 2 ≠ 0), mul_zero]

theorem quadratic_nonneg {v : E} (hv : v ∈ positive T hT) : 0 ≤ ⟪T v, v⟫ := by
  rw [quadratic_eq_sum T hT]
  apply Finset.sum_nonneg
  intro i hi
  by_cases hev : 0 < hT.eigenvalues rfl i
  · exact mul_nonneg hev.le (sq_nonneg _)
  · rw [repr_zero_of_not_mem T hT hv hev, zero_pow (by decide : 2 ≠ 0), mul_zero]

theorem quadratic_eq_zero_iff {v : E} (hv : v ∈ nonpositive T hT) :
    ⟪T v, v⟫ = 0 ↔ T v = 0 := by
  constructor
  · intro hz
    rw [quadratic_eq_sum T hT] at hz
    have hterms : ∀ i ∈ Finset.univ,
        hT.eigenvalues rfl i * ((hT.eigenvectorBasis rfl).repr v i) ^ 2 ≤ 0 := by
      intro i hi
      by_cases hev : hT.eigenvalues rfl i ≤ 0
      · exact mul_nonpos_of_nonpos_of_nonneg hev (sq_nonneg _)
      · rw [repr_zero_of_not_mem T hT hv hev, zero_pow (by decide : 2 ≠ 0), mul_zero]
    have heach := (Finset.sum_eq_zero_iff_of_nonpos hterms).mp hz
    apply (hT.eigenvectorBasis rfl).repr.injective
    ext i
    rw [repr_apply T hT, map_zero]
    have h := heach i (Finset.mem_univ i)
    rcases mul_eq_zero.mp h with hev | hc
    · simp [hev]
    · have hc0 : (hT.eigenvectorBasis rfl).repr v i = 0 := by nlinarith
      simp [hc0]
  · intro hz
    rw [hz, inner_zero_left]

theorem finrank_nonpositive : finrank ℝ (nonpositive T hT) =
    finrank ℝ (negative T hT) + finrank ℝ (LinearMap.ker T.toLinearMap) := by
  have hd : Disjoint (negative T hT) (LinearMap.ker T.toLinearMap) :=
    (transverse_isCompl_ker T hT).disjoint.mono_left le_sup_left
  rw [nonpositive_eq]
  have hi : negative T hT ⊓ LinearMap.ker T.toLinearMap = ⊥ := hd.eq_bot
  have hr := Submodule.finrank_sup_add_finrank_inf_eq (negative T hT) (LinearMap.ker T.toLinearMap)
  rw [hi, finrank_bot, add_zero] at hr
  exact hr

/-- An actual continuous linear change of coordinates, including singular Hessians. -/
def splitEquiv : E ≃L[ℝ] (nonpositive T hT × positive T hT) :=
  ((nonpositive T hT).prodEquivOfIsCompl (positive T hT)
    (nonpositive_isCompl_positive T hT)).toContinuousLinearEquiv.symm

theorem splitEquiv_symm_apply (u : nonpositive T hT) (v : positive T hT) :
    (splitEquiv T hT).symm (u, v) = (u : E) + (v : E) := rfl

theorem nonpositive_inner_positive {u v : E}
    (hu : u ∈ nonpositive T hT) (hv : v ∈ positive T hT) : ⟪u, v⟫ = 0 :=
  spectral_inner_eq_zero T hT
    (s := {i | hT.eigenvalues rfl i ≤ 0}) (t := {i | 0 < hT.eigenvalues rfl i})
    (Set.disjoint_left.mpr (fun i hi hj =>
      not_lt_of_ge (show hT.eigenvalues rfl i ≤ 0 from hi) hj)) hu hv

theorem quadratic_add (u : nonpositive T hT) (v : positive T hT) :
    ⟪T ((u : E) + v), (u : E) + v⟫ = ⟪T u, (u : E)⟫ + ⟪T v, (v : E)⟫ := by
  have hu : T u ∈ nonpositive T hT :=
    hT.map_eigenvectorSpan_le rfl _ (Submodule.mem_map.mpr ⟨u, u.property, rfl⟩)
  have huv := nonpositive_inner_positive T hT hu v.property
  have hvu : ⟪T v, (u : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact nonpositive_inner_positive T hT u.property (map_positive_mem T hT v.property)
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, huv, hvu]
  ring

theorem kerProj_positive (v : positive T hT) : kerProj T (v : E) = 0 := by
  have hv : (v : E) ∈ (LinearMap.ker T.toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    exact nonpositive_inner_positive T hT (by rw [nonpositive_eq]; exact Submodule.mem_sup_right hu)
      v.property
  simpa only [kerProj, Submodule.starProjection_apply, Submodule.coe_zero] using
    congrArg Subtype.val (Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv)

/-- The reduced function plus the negative quadratic form on the whole
nonpositive space. The kernel projection is the genuine orthogonal projection. -/
def reducedPart (R : E → ℝ) (u : nonpositive T hT) : ℝ :=
  R (kerProj T u) + 1 / 2 * ⟪T u, (u : E)⟫

theorem reducedPart_zero (R : E → ℝ) : reducedPart T hT R 0 = R 0 := by
  simp [reducedPart]

/-- Strict maximality on the kernel extends to all negative and zero
directions. This includes the zero-dimensional kernel without a special case. -/
theorem reducedPart_strict_max (R : E → ℝ)
    (hmax : ∀ᶠ (z : LinearMap.ker T.toLinearMap) in 𝓝 0, z ≠ 0 → R z < R 0) :
    ∀ᶠ u in 𝓝 (0 : nonpositive T hT), u ≠ 0 →
      reducedPart T hT R u < reducedPart T hT R 0 := by
  let k : nonpositive T hT → LinearMap.ker T.toLinearMap :=
    fun u => ⟨kerProj T u, map_kerProj T u⟩
  have hk : Continuous k := ((kerProj T).continuous.comp continuous_subtype_val).subtype_mk _
  have hk0 : k 0 = 0 := by apply Subtype.ext; exact map_zero _
  have hkt : Tendsto k (𝓝 0) (𝓝 0) := by
    simpa only [hk0] using hk.continuousAt.tendsto (x := 0)
  have hnear := hkt.eventually hmax
  filter_upwards [hnear] with u hu hune
  rw [reducedPart_zero, reducedPart]
  have hq := quadratic_nonpos T hT u.property
  by_cases hz : k u = 0
  · have hp0 : kerProj T (u : E) = 0 := congrArg Subtype.val hz
    have hTne : T u ≠ 0 := by
      intro hTu
      apply hune
      apply Subtype.ext
      rw [← kerProj_of_map_eq_zero T hTu, hp0]
      rfl
    have hqne := (quadratic_eq_zero_iff T hT u.property).not.mpr hTne
    rw [hp0]
    have hqneg := lt_of_le_of_ne hq hqne
    linarith
  · have hR := hu hz
    change R (kerProj T u) < R 0 at hR
    linarith

/-- The spectral energy splits with no mixed quadratic term. -/
theorem energy_split (R : E → ℝ) (u : nonpositive T hT) (v : positive T hT) :
    R (kerProj T ((u : E) + v)) + 1 / 2 * ⟪T ((u : E) + v), (u : E) + v⟫ =
      reducedPart T hT R u + 1 / 2 * ⟪T v, (v : E)⟫ := by
  rw [map_add, kerProj_positive T hT v, add_zero, quadratic_add T hT u v, reducedPart]
  ring

/-- Spectral coordinates with the nonpositive factor identified with the
standard Euclidean space used by relative disk homology. -/
def diskCoordinates : E ≃L[ℝ]
    (EuclideanSpace ℝ (Fin (finrank ℝ (nonpositive T hT))) × positive T hT) :=
  (splitEquiv T hT).trans
    ((stdOrthonormalBasis ℝ (nonpositive T hT)).repr.toContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (positive T hT)))

theorem diskCoordinates_symm_apply
    (u : EuclideanSpace ℝ (Fin (finrank ℝ (nonpositive T hT)))) (v : positive T hT) :
    (diskCoordinates T hT).symm (u, v) =
      (((stdOrthonormalBasis ℝ (nonpositive T hT)).repr.symm u : nonpositive T hT) : E) + v := rfl

/-- Construct the disk and detector directly from a degenerate splitting
chart and strict maximality on its kernel. For a geodesic, such a chart is
needed on a transverse slice, together with a proved maximum hypothesis. -/
theorem nonempty_maximalDiskData_of_spectralSplitting
    {X : Type} [TopologicalSpace X] (energy : X → ℝ) (p : X)
    (e : OpenPartialHomeomorph X E) (hp : p ∈ e.source) (he : e p = 0)
    (R : E → ℝ)
    (henergy : ∀ x ∈ e.source,
      energy x = R (kerProj T (e x)) + 1 / 2 * ⟪T (e x), e x⟫)
    (hmax : ∀ᶠ (z : LinearMap.ker T.toLinearMap) in 𝓝 0, z ≠ 0 → R z < R 0) :
    Nonempty (MaximalDiskData energy p (finrank ℝ (nonpositive T hT))) := by
  let b := (stdOrthonormalBasis ℝ (nonpositive T hT)).repr
  let c := diskCoordinates T hT
  let chart := e.trans c.toHomeomorph.toOpenPartialHomeomorph
  apply nonempty_maximalDiskData_of_normalForm energy p (0 : positive T hT) chart
    ⟨hp, mem_univ _⟩ (by change c (e p) = (0, 0); rw [he, map_zero]; rfl)
    (fun u => reducedPart T hT R (b.symm u)) (fun v : positive T hT => 1 / 2 * ⟪T v, (v : E)⟫)
  · intro x hx
    rw [henergy x hx.1]
    have hc : e x = (c.symm (c (e x))) := (c.symm_apply_apply (e x)).symm
    conv_lhs => rw [hc]
    rw [← Prod.eta (c (e x)), diskCoordinates_symm_apply, energy_split]
    rfl
  · have hb : Tendsto b.symm (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using b.symm.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [hb.eventually (reducedPart_strict_max T hT R hmax)] with u hu hune
    simpa only [map_zero] using hu (fun h => hune (b.symm.injective (h.trans (map_zero _).symm)))
  · intro v hv
    have hq := quadratic_nonneg T hT v.property
    simp only [Submodule.coe_zero, map_zero, inner_zero_left, mul_zero]
    positivity

section Phase

/-- The hyperplane perpendicular to a chosen nonzero phase vector. -/
def phaseSlice (v : E) : Submodule ℝ E := (ℝ ∙ v)ᗮ

variable {T hT} (v : E) (hv : T v = 0)

omit [FiniteDimensional ℝ E] in
include hT hv in
/-- The image of the Hessian is perpendicular to any kernel vector. -/
theorem map_mem_phaseSlice (w : E) : T w ∈ phaseSlice v := by
  rw [phaseSlice, Submodule.mem_orthogonal_singleton_iff_inner_left]
  calc
    ⟪T w, v⟫ = ⟪w, T v⟫ := hT w v
    _ = 0 := by rw [hv, inner_zero_right]

/-- The actual restriction of the Hessian to the phase hyperplane. -/
def phaseRestriction : phaseSlice v →L[ℝ] phaseSlice v :=
  (T.comp (phaseSlice v).subtypeL).codRestrict (phaseSlice v)
    (fun w => map_mem_phaseSlice (hT := hT) v hv w)

omit [FiniteDimensional ℝ E] in
theorem phaseRestriction_apply (w : phaseSlice v) :
    (phaseRestriction (hT := hT) v hv w : E) = T w := rfl

omit [FiniteDimensional ℝ E] in
theorem phaseRestriction_symmetric :
    (phaseRestriction (hT := hT) v hv).toLinearMap.IsSymmetric := by
  intro w z
  exact hT (w : E) (z : E)

/-- The kernel after phase removal is the original kernel intersected with
the phase hyperplane, here expressed as an orthogonal complement inside
the original kernel. This identifies the actual linear maps, not just ranks. -/
def phaseKernelEquiv :
    LinearMap.ker (phaseRestriction (hT := hT) v hv).toLinearMap ≃ₗ[ℝ]
      (ℝ ∙ (⟨v, hv⟩ : LinearMap.ker T.toLinearMap))ᗮ where
  toFun w := ⟨⟨w.val.val, congrArg Subtype.val w.property⟩, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    change ⟪(w.val.val : E), v⟫ = 0
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.val.property⟩
  invFun w := ⟨⟨w.val.val, by
    rw [phaseSlice, Submodule.mem_orthogonal_singleton_iff_inner_left]
    have h : ⟪(w.val : LinearMap.ker T.toLinearMap),
        (⟨v, hv⟩ : LinearMap.ker T.toLinearMap)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.property
    exact h⟩,
    Subtype.ext w.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Removing one nonzero phase direction decreases nullity by exactly one.
This is the dimension correction needed before a maximal characteristic
disk can be used for an unparametrized closed geodesic. -/
theorem phaseRestriction_nullity (hne : v ≠ 0) :
    finrank ℝ (LinearMap.ker (phaseRestriction (hT := hT) v hv).toLinearMap) + 1 =
      finrank ℝ (LinearMap.ker T.toLinearMap) := by
  rw [(phaseKernelEquiv (hT := hT) v hv).finrank_eq]
  have hn : (⟨v, hv⟩ : LinearMap.ker T.toLinearMap) ≠ 0 :=
    fun h => hne (congrArg Subtype.val h)
  have h := (ℝ ∙ (⟨v, hv⟩ : LinearMap.ker T.toLinearMap)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hn] at h
  omega

end Phase

end

end Finsler.SurfaceSpectralDisk
