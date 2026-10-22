import SurfacePhaseGeometry
import Finsler.Geometry.PolygonNormal

/-!
# Iteration on phase-transverse spaces

Removing a kernel phase direction preserves the negative index. A conformal
linear embedding intertwining Hessians induces an embedding of the transverse
spaces and, when nullity does not increase, an actual equivalence of their
kernels. These constructions apply to the genuine polygon iteration map.
-/

namespace Finsler.SurfaceIteration

open Set Filter Module
open Finsler.SurfaceSpectralDisk Finsler.SurfacePhaseGeometry
open Finsler.LyapunovSchmidt Finsler.OperatorIndex
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true

section Index
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hs : T.toLinearMap.IsSymmetric)
  (v : E) (hv : T v = 0)

/-- Removing a phase direction in the kernel leaves the negative index
unchanged. The direction need not be nonzero for this index identity. -/
theorem phaseRestriction_index :
    finrank ℝ (HessianSplitting.negative (phaseRestriction (hT := hs) v hv)
      (phaseRestriction_symmetric (hT := hs) v hv)) =
        finrank ℝ (HessianSplitting.negative T hs) := by
  have hK : ∀ w ∈ (ℝ ∙ v), T w ∈ (ℝ ∙ v) := by
    intro w hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp only [map_smul, hv, smul_zero]
    exact Submodule.zero_mem _
  have hz : sigNeg ((quad T).restrict (ℝ ∙ v)) = 0 := by
    apply (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero _).mp
    intro w
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp w.property
    change 0 ≤ ⟪T (w : E), (w : E)⟫
    rw [← hr, map_smul, hv, smul_zero, inner_zero_left]
  have he : quad (phaseRestriction (hT := hs) v hv) = (quad T).restrict (phaseSlice v) := by
    ext w
    rfl
  rw [OperatorIndex.finrank_negative, OperatorIndex.finrank_negative, he,
    InvariantIndex.sigNeg_quad_eq_add hs hK, hz, zero_add]
  rfl

end Index

section Conformal
variable {E₀ E : Type} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
  [FiniteDimensional ℝ E₀] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  (L : E₀ →L[ℝ] E) {κ : ℝ} (hL : ∀ x y, ⟪L x, L y⟫ = κ * ⟪x, y⟫) (v : E₀)

/-- The iteration embedding restricted to the hyperplanes perpendicular
to the original and iterated phase vectors. -/
def sliceMap : phaseSlice v →L[ℝ] phaseSlice (L v) :=
  (L.comp (phaseSlice v).subtypeL).codRestrict (phaseSlice (L v)) (fun w => by
    rw [phaseSlice, Submodule.mem_orthogonal_singleton_iff_inner_left]
    change ⟪L (w : E₀), L v⟫ = 0
    rw [hL, Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.property, mul_zero])

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
theorem sliceMap_apply (w : phaseSlice v) : (sliceMap L hL v w : E) = L w := rfl

include hL in
omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
theorem sliceMap_inner (x y : phaseSlice v) :
    ⟪sliceMap L hL v x, sliceMap L hL v y⟫ = κ * ⟪x, y⟫ := hL x y

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
theorem sliceMap_injective (hinj : Function.Injective L) : Function.Injective (sliceMap L hL v) :=
  fun _ _ h => Subtype.ext (hinj (congrArg Subtype.val h))

set_option backward.isDefEq.respectTransparency false in
/-- Orthogonal projection off the phase direction commutes with the
conformal embedding, including for vectors outside the transverse space. -/
theorem phase_projection_map (x : E₀) :
    (phaseSlice (L v)).orthogonalProjectionOnto (L x) =
      sliceMap L hL v ((phaseSlice v).orthogonalProjectionOnto x) := by
  apply Subtype.ext
  change (phaseSlice (L v)).starProjection (L x) =
    L ((phaseSlice v).orthogonalProjectionOnto x)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact (sliceMap L hL v ((phaseSlice v).orthogonalProjectionOnto x)).property
  · have hr : x - ((phaseSlice v).orthogonalProjectionOnto x : E₀) ∈ (ℝ ∙ v) := by
      simpa only [phaseSlice, Submodule.orthogonal_orthogonal, Submodule.starProjection_apply] using
        (Submodule.sub_starProjection_mem_orthogonal (K := phaseSlice v) x)
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hr
    rw [← map_sub, ← hr, map_smul]
    exact (phaseSlice (L v))ᗮ.smul_mem r
      (by change L v ∈ (ℝ ∙ L v)ᗮᗮ; exact Submodule.le_orthogonal_orthogonal _ (Submodule.mem_span_singleton_self _))

variable {A₀ : E₀ →L[ℝ] E₀} {A : E →L[ℝ] E}
  (hs₀ : A₀.toLinearMap.IsSymmetric) (hs : A.toLinearMap.IsSymmetric)
  (hv : A₀ v = 0) {c : ℝ} (hA : ∀ x, A (L x) = c • L (A₀ x))

include hA hv in
omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
theorem phase_image_mem_kernel : A (L v) = 0 := by rw [hA, hv, map_zero, smul_zero]

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E] in
/-- Hessian intertwining survives the removal of the actual phase lines. -/
theorem slice_hessian_map (x : phaseSlice v) :
    phaseRestriction (hT := hs) (L v) (phase_image_mem_kernel L v hv hA) (sliceMap L hL v x) =
      c • sliceMap L hL v (phaseRestriction (hT := hs₀) v hv x) :=
  Subtype.ext (hA x)

/-- If the full nullities agree, the transverse nullities agree as well.
Both phase vectors are proved nonzero using the embedding's injectivity. -/
theorem slice_nullity_eq (hinj : Function.Injective L) (hne : v ≠ 0)
    (hnull : finrank ℝ (LinearMap.ker A.toLinearMap) ≤ finrank ℝ (LinearMap.ker A₀.toLinearMap)) :
    finrank ℝ (LinearMap.ker
      (phaseRestriction (hT := hs) (L v) (phase_image_mem_kernel L v hv hA)).toLinearMap) =
    finrank ℝ (LinearMap.ker (phaseRestriction (hT := hs₀) v hv).toLinearMap) := by
  have hne' : L v ≠ 0 := fun h => hne (hinj (h.trans (map_zero L).symm))
  have h₀ := phaseRestriction_nullity (hT := hs₀) v hv hne
  have h₁ := phaseRestriction_nullity (hT := hs) (L v) (phase_image_mem_kernel L v hv hA) hne'
  have hle := ReductionNaturality.finrank_ker_le hA hinj
  omega

/-- The induced map between the actual transverse kernels. -/
def sliceKernelMap :
    LinearMap.ker (phaseRestriction (hT := hs₀) v hv).toLinearMap →ₗ[ℝ]
    LinearMap.ker (phaseRestriction (hT := hs) (L v) (phase_image_mem_kernel L v hv hA)).toLinearMap :=
  (sliceMap L hL v).toLinearMap.restrict (fun x hx => by
    change phaseRestriction (hT := hs₀) v hv x = 0 at hx
    change phaseRestriction (hT := hs) (L v) (phase_image_mem_kernel L v hv hA) (sliceMap L hL v x) = 0
    rw [slice_hessian_map L hL v hs₀ hs hv hA, hx, map_zero, smul_zero])

/-- Stable nullity gives an actual continuous linear equivalence of the
transverse kernels, with forward map equal to the original iteration map. -/
def sliceKernelEquiv (hinj : Function.Injective L) (hne : v ≠ 0)
    (hnull : finrank ℝ (LinearMap.ker A.toLinearMap) ≤ finrank ℝ (LinearMap.ker A₀.toLinearMap)) :
    LinearMap.ker (phaseRestriction (hT := hs₀) v hv).toLinearMap ≃L[ℝ]
    LinearMap.ker (phaseRestriction (hT := hs) (L v) (phase_image_mem_kernel L v hv hA)).toLinearMap := by
  let f := sliceKernelMap L hL v hs₀ hs hv hA
  have hi : Function.Injective f := fun x y h => Subtype.ext
    (sliceMap_injective L hL v hinj (congrArg Subtype.val h))
  have hd := slice_nullity_eq L v hs₀ hs hv hA hinj hne hnull
  exact (LinearEquiv.ofBijective f ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd.symm).mp hi⟩).toContinuousLinearEquiv

theorem sliceKernelEquiv_apply (hinj : Function.Injective L) (hne : v ≠ 0)
    (hnull : finrank ℝ (LinearMap.ker A.toLinearMap) ≤ finrank ℝ (LinearMap.ker A₀.toLinearMap))
    (x : LinearMap.ker (phaseRestriction (hT := hs₀) v hv).toLinearMap) :
    ((sliceKernelEquiv L hL v hs₀ hs hv hA hinj hne hnull x).val : E) = L (x.val : E₀) := rfl

end Conformal

section SliceAnalysis
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Restrict the translated function to the actual orthogonal phase slice. -/
def sliceEnergy (f : E → ℝ) (p v : E) (w : phaseSlice v) : ℝ := f (p + (w : E))

/-- Project the translated gradient to the same slice. -/
def sliceGradient (G : E → E) (p v : E) (w : phaseSlice v) : phaseSlice v :=
  (phaseSlice v).orthogonalProjectionOnto (G (p + (w : E)))

variable {f : E → ℝ} {G : E → E} {p : E} {A : E →L[ℝ] E}
  (hs : A.toLinearMap.IsSymmetric) (v : E) (hv : A v = 0)

theorem sliceGradient_smooth (hG : ContDiffAt ℝ 2 G p) :
    ContDiffAt ℝ 2 (sliceGradient G p v) 0 := by
  have hG' : ContDiffAt ℝ 2 G (p + ((0 : phaseSlice v) : E)) := by simpa using hG
  exact (phaseSlice v).orthogonalProjectionOnto.contDiff.contDiffAt.comp (0 : phaseSlice v)
    (hG'.comp (0 : phaseSlice v) (contDiffAt_const.add (phaseSlice v).subtypeL.contDiff.contDiffAt))

theorem sliceGradient_zero (hG : G p = 0) : sliceGradient G p v 0 = 0 := by
  simp only [sliceGradient, Submodule.coe_zero, add_zero, hG, map_zero]

theorem sliceGradient_derivative (hA : HasFDerivAt G A p) :
    HasFDerivAt (sliceGradient G p v) (phaseRestriction (hT := hs) v hv) 0 := by
  have hi : HasFDerivAt (fun w : phaseSlice v => p + (w : E)) (phaseSlice v).subtypeL 0 :=
    (phaseSlice v).subtypeL.hasFDerivAt.const_add p
  have hA' : HasFDerivAt G A (p + ((0 : phaseSlice v) : E)) := by simpa using hA
  have hd := (phaseSlice v).orthogonalProjectionOnto.hasFDerivAt.comp (0 : phaseSlice v)
    (hA'.comp (0 : phaseSlice v) hi)
  have he : (phaseSlice v).orthogonalProjectionOnto.comp (A.comp (phaseSlice v).subtypeL) =
      phaseRestriction (hT := hs) v hv := by
    apply ContinuousLinearMap.ext
    intro w
    change (phaseSlice v).orthogonalProjectionOnto
      ((phaseRestriction (hT := hs) v hv w : phaseSlice v) : E) = _
    exact (phaseSlice v).orthogonalProjectionOnto_mem_subspace_eq_self _
  rwa [he] at hd

theorem sliceEnergy_derivative
    (hf : ∀ᶠ x in 𝓝 p, HasFDerivAt f (innerSL ℝ (G x)) x) :
    ∀ᶠ w in 𝓝 (0 : phaseSlice v),
      HasFDerivAt (sliceEnergy f p v) (innerSL ℝ (sliceGradient G p v w)) w := by
  have hc : Continuous (fun w : phaseSlice v => p + (w : E)) :=
    continuous_const.add (phaseSlice v).subtypeL.continuous
  have ht : Tendsto (fun w : phaseSlice v => p + (w : E)) (𝓝 0) (𝓝 p) := by
    simpa only [Submodule.coe_zero, add_zero] using hc.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually hf] with w hw
  change HasFDerivAt f (innerSL ℝ (G (p + (w : E)))) (p + (w : E)) at hw
  have hi : HasFDerivAt (fun w : phaseSlice v => p + (w : E)) (phaseSlice v).subtypeL w :=
    (phaseSlice v).subtypeL.hasFDerivAt.const_add p
  have hd := hw.comp w hi
  have he : (innerSL ℝ (G (p + (w : E)))).comp (phaseSlice v).subtypeL =
      innerSL ℝ (sliceGradient G p v w) := by
    apply ContinuousLinearMap.ext
    intro u
    exact ((phaseSlice v).inner_orthogonalProjectionOnto_eq_of_mem_right u _).symm
  rwa [he] at hd

end SliceAnalysis

section Reduction
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Reduction data retaining the inverse identities needed to compare
iterations and the derivative needed for a splitting with this same map. -/
structure ReductionData (A : E →L[ℝ] E) (hs : A.toLinearMap.IsSymmetric) (G : E → E) where
  reduction : E → E
  smooth : ContDiffAt ℝ 2 reduction 0
  zero : reduction 0 = 0
  derivative : HasStrictFDerivAt reduction ((linEquiv hs).symm : E →L[ℝ] E) 0
  right_inverse : ∀ᶠ w in 𝓝 (0 : E),
    kerProj A (reduction w) = kerProj A w ∧ cokerProj A (G (reduction w)) = cokerProj A w
  left_inverse : ∀ᶠ z in 𝓝 (0 : E), reduction (kerProj A z + cokerProj A (G z)) = z

variable {A : E →L[ℝ] E} (hs : A.toLinearMap.IsSymmetric) {G : E → E}

theorem nonempty_reductionData (hG : ContDiffAt ℝ 2 G 0) (hA : HasFDerivAt G A 0) (h0 : G 0 = 0) :
    Nonempty (ReductionData A hs G) := by
  obtain ⟨σ, hσ, hσ0, hd, hr, hl⟩ := exists_reduction hs (k := 2) (by norm_num) hG hA h0
  exact ⟨⟨σ, hσ, hσ0, hd, by simpa only [zero_add] using hr,
    by simpa only [zero_add] using hl⟩⟩

/-- Construct a splitting for the specified reduction, so that the reduced
function compared under iteration is exactly the one used for a disk. -/
theorem ReductionData.exists_splitting (D : ReductionData A hs G)
    (hG : ContDiffAt ℝ 2 G 0) (hA : HasFDerivAt G A 0) (h0 : G 0 = 0)
    {f : E → ℝ} (hf : ∀ᶠ x in 𝓝 (0 : E), HasFDerivAt f (innerSL ℝ (G x)) x) :
    ∃ e : OpenPartialHomeomorph E E, 0 ∈ e.source ∧ e 0 = 0 ∧
      ∀ x ∈ e.source, f x = f (D.reduction (kerProj A (e x))) + 1 / 2 * ⟪A (e x), e x⟫ := by
  have hr : ∀ᶠ w in 𝓝 (0 : E), kerProj A (D.reduction w) = kerProj A w ∧
      cokerProj A (G (0 + D.reduction w)) = cokerProj A w := by simpa only [zero_add] using D.right_inverse
  have hl : ∀ᶠ z in 𝓝 (0 : E), D.reduction (kerProj A z + cokerProj A (G (0 + z))) = z := by
    simpa only [zero_add] using D.left_inverse
  obtain ⟨Ξ, -, hΞ0, hΞd, hΞP, hΞf⟩ :=
    SplittingLemma.exists_chart hs hG hA h0 hf D.smooth D.zero D.derivative hr hl
  obtain ⟨s, hs', hopen, hmem⟩ := eventually_nhds_iff.mp (hΞP.and hΞf)
  have hd : HasStrictFDerivAt Ξ
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := hΞd
  let e := (hd.toOpenPartialHomeomorph Ξ).restrOpen s hopen
  refine ⟨e, ⟨hd.mem_toOpenPartialHomeomorph_source, hmem⟩, hΞ0, ?_⟩
  intro x hx
  obtain ⟨hP, hF⟩ := hs' x hx.2
  change f x = f (D.reduction (kerProj A (Ξ x))) + 1 / 2 * ⟪A (Ξ x), Ξ x⟫
  simpa only [zero_add, ← hP] using hF

/-- A strict maximum of this reduction constructs a maximal disk on the
actual domain of the function. The maximum remains an explicit input. -/
theorem ReductionData.maximalDisk (D : ReductionData A hs G)
    (hG : ContDiffAt ℝ 2 G 0) (hA : HasFDerivAt G A 0) (h0 : G 0 = 0)
    {f : E → ℝ} (hf : ∀ᶠ x in 𝓝 (0 : E), HasFDerivAt f (innerSL ℝ (G x)) x)
    (hmax : ∀ᶠ (z : LinearMap.ker A.toLinearMap) in 𝓝 0,
      z ≠ 0 → f (D.reduction z) < f (D.reduction 0)) :
    Nonempty (SurfaceMorseData.MaximalDiskData f 0
      (finrank ℝ (HessianSplitting.negative A hs) + finrank ℝ (LinearMap.ker A.toLinearMap))) := by
  obtain ⟨e, hmem, he, hE⟩ := D.exists_splitting hs hG hA h0 hf
  have hd := nonempty_maximalDiskData_of_spectralSplitting A hs f 0 e hmem he
    (fun z => f (D.reduction z)) hE hmax
  simpa only [finrank_nonpositive] using hd

end Reduction

section Transport
variable {K₀ K : Type} [NormedAddCommGroup K₀] [NormedSpace ℝ K₀]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Positive scaling and a genuine equivalence of kernel neighborhoods
transport a strict reduced maximum. A dimension count alone is insufficient. -/
theorem strict_max_of_equiv (e : K₀ ≃L[ℝ] K) {R₀ : K₀ → ℝ} {R : K → ℝ}
    {d : ℝ} (hd : 0 < d) (he : ∀ᶠ z in 𝓝 (0 : K₀), R (e z) = d * R₀ z)
    (hmax : ∀ᶠ z in 𝓝 (0 : K₀), z ≠ 0 → R₀ z < R₀ 0) :
    ∀ᶠ z in 𝓝 (0 : K), z ≠ 0 → R z < R 0 := by
  have hzero : R 0 = d * R₀ 0 := by simpa only [map_zero] using he.self_of_nhds
  have ht : Tendsto e.symm (𝓝 (0 : K)) (𝓝 (0 : K₀)) := by
    simpa only [map_zero] using e.symm.continuous.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually he, ht.eventually hmax] with z hz hm hne
  rw [e.apply_symm_apply] at hz
  rw [hz, hzero]
  apply mul_lt_mul_of_pos_left _ hd
  exact hm (fun h => hne (e.symm.injective (h.trans (map_zero e.symm).symm)))

end Transport

section Polygon
open Finsler.Geometry Finsler.SphereGeometry Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonIterate
open Finsler.PolygonIterateReduction Finsler.AmbientRotation

variable {n N : ℕ} [NeZero N] {F : ReversibleMetric n}

/-- A stationary actual short polygon with its specified nonzero kernel
phase vector. Every sampled regular geodesic supplies this data. -/
structure PolygonSlice (F : ReversibleMetric n) (N : ℕ) [NeZero N] where
  segments : PolygonModel.SegmentData F
  point : ZMod N → Sphere n
  short : ShortPolygon segments.δ point
  nonzero_edges : ∀ i, point (i + 1) ≠ point i
  critical : PolyCritical F N point
  phase : Model n N
  phase_ne_zero : phase ≠ 0
  phase_kernel : hessian F point phase = 0

namespace PolygonSlice

/-- The phase direction is the derivative of the original rotation family,
not an arbitrary extra kernel hypothesis for a closed geodesic. -/
def ofGeodesic {g : Geodesics.ClosedGeodesic F} {a : ℝ} (D : GeodesicPhaseModel F g a) :
    PolygonSlice F D.vertices where
  segments := D.model.toSegmentData
  point := (phasePoint D 0).val
  short := (phasePoint D 0).property
  nonzero_edges := phasePoint_nonzero_edges D 0
  critical := phasePoint_critical D 0
  phase := phaseVector D.vertices g.loop
  phase_ne_zero := phaseVector_ne_zero D.vertices g.loop g.regular
  phase_kernel := phaseVector_mem_ker F D.model.toSegmentData g D.facts

/-- The sampled geodesic supplies the twist condition needed by the
monodromy nullity theorem. It is not an additional geodesic hypothesis. -/
theorem ofGeodesic_twist {g : Geodesics.ClosedGeodesic F} {a : ℝ}
    (D : GeodesicPhaseModel F g a) : PolygonNullity.Twist F (ofGeodesic D).point := by
  change PolygonNullity.Twist F (phasePolygon D.vertices g.loop 0)
  rw [phasePolygon_eq_sample]
  exact (D.facts 0).2.2.2.1

variable (P : PolygonSlice F N)

theorem symmetric : (hessian F P.point).toLinearMap.IsSymmetric :=
  hessian_isSymmetric F P.segments.smooth P.short P.nonzero_edges

def operator : phaseSlice P.phase →L[ℝ] phaseSlice P.phase :=
  phaseRestriction (hT := P.symmetric) P.phase P.phase_kernel

def energy : phaseSlice P.phase → ℝ := sliceEnergy (PolygonChart.energy F P.point) (base P.point) P.phase

def gradient : phaseSlice P.phase → phaseSlice P.phase := sliceGradient (grad F P.point) (base P.point) P.phase

theorem operator_symmetric : LinearMap.IsSymmetric (E := phaseSlice P.phase) P.operator.toLinearMap :=
  phaseRestriction_symmetric (hT := P.symmetric) P.phase P.phase_kernel

theorem operator_index :
    finrank ℝ (HessianSplitting.negative P.operator P.operator_symmetric) =
      index F P.point P.symmetric := phaseRestriction_index P.symmetric P.phase P.phase_kernel

theorem operator_nullity : finrank ℝ (LinearMap.ker P.operator.toLinearMap) + 1 = nullity F P.point :=
  phaseRestriction_nullity (hT := P.symmetric) P.phase P.phase_kernel P.phase_ne_zero

theorem gradient_smooth : ContDiffAt ℝ 2 P.gradient 0 :=
  sliceGradient_smooth P.phase (grad_contDiffAt F P.segments.smooth P.short P.nonzero_edges)

theorem gradient_zero : P.gradient 0 = 0 :=
  sliceGradient_zero P.phase
    (grad_eq_zero_of_polyCritical F P.segments.smooth P.short P.nonzero_edges P.critical)

theorem gradient_derivative : HasFDerivAt P.gradient P.operator 0 :=
  sliceGradient_derivative P.symmetric P.phase P.phase_kernel
    (grad_hasFDerivAt F P.segments.smooth P.short P.nonzero_edges)

theorem energy_derivative :
    ∀ᶠ w in 𝓝 (0 : phaseSlice P.phase), HasFDerivAt P.energy (innerSL ℝ (P.gradient w)) w :=
  sliceEnergy_derivative P.phase (eventually_hasFDerivAt F P.segments.smooth P.short P.nonzero_edges)

theorem nonempty_reduction : Nonempty (ReductionData P.operator P.operator_symmetric P.gradient) :=
  nonempty_reductionData P.operator_symmetric P.gradient_smooth P.gradient_derivative P.gradient_zero

/-- Repeating the polygon repeats the actual phase curve; its tangent is
`iterL phase`. The resulting data is again a stationary short polygon. -/
def iterated (m : ℕ) [NeZero m] : PolygonSlice F (m * N) where
  segments := P.segments
  point := PolygonIterate.iterate m N P.point
  short := shortPolygon_iterate m N P.short
  nonzero_edges := iterate_ne m N P.nonzero_edges
  critical := polyCritical_iterate m F P.segments.smooth P.short P.nonzero_edges P.critical
  phase := iterL m N P.phase
  phase_ne_zero := fun h => P.phase_ne_zero (iterL_injective m N (h.trans (map_zero _).symm))
  phase_kernel := by rw [hessian_iterate m N F P.segments.smooth P.short P.nonzero_edges,
    P.phase_kernel, map_zero, smul_zero]

variable (m : ℕ) [NeZero m]

def iterationMap : phaseSlice P.phase →L[ℝ] phaseSlice (P.iterated m).phase :=
  sliceMap (iterL m N) (inner_iterL m N) P.phase

theorem iterationMap_injective : Function.Injective (P.iterationMap m) :=
  sliceMap_injective _ _ _ (iterL_injective m N)

theorem iterationMap_inner (x y : phaseSlice P.phase) :
    ⟪P.iterationMap m x, P.iterationMap m y⟫ = (m : ℝ) * ⟪x, y⟫ := by
  change ⟪iterL m N (x : Model n N), iterL m N (y : Model n N)⟫ = (m : ℝ) * ⟪(x : Model n N), (y : Model n N)⟫
  exact inner_iterL (n := n) m N (x : Model n N) (y : Model n N)

theorem energy_iteration (w : phaseSlice P.phase) :
    (P.iterated m).energy (P.iterationMap m w) = (m : ℝ) ^ 2 * P.energy w := by
  change PolygonChart.energy F (PolygonIterate.iterate m N P.point)
    (base (PolygonIterate.iterate m N P.point) + iterL m N (w : Model n N)) = _
  rw [base_iterate, ← map_add, PolygonIterate.energy_iterate]
  rfl

/-- The projected gradients, not only the full polygon gradients, intertwine
under iteration. This is the input needed for transverse reduction maps. -/
theorem gradient_iteration :
    ∀ᶠ w in 𝓝 (0 : phaseSlice P.phase),
      (P.iterated m).gradient (P.iterationMap m w) = (m : ℝ) • P.iterationMap m (P.gradient w) := by
  have ht : Tendsto (phaseSlice P.phase).subtypeL (𝓝 0) (𝓝 (0 : Model n N)) := by
    simpa only [map_zero] using (phaseSlice P.phase).subtypeL.continuous.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (eventually_grad_iterate_add m N F P.segments.smooth P.short P.nonzero_edges)] with w hw
  change grad F (PolygonIterate.iterate m N P.point)
    (base (PolygonIterate.iterate m N P.point) + iterL m N (w : Model n N)) =
    (m : ℝ) • iterL m N (grad F P.point (base P.point + (w : Model n N))) at hw
  change (phaseSlice (iterL m N P.phase)).orthogonalProjectionOnto
    (grad F (PolygonIterate.iterate m N P.point)
      (base (PolygonIterate.iterate m N P.point) + iterL m N (w : Model n N))) = _
  rw [hw, map_smul, phase_projection_map (iterL m N) (inner_iterL m N) P.phase]
  rfl

theorem operator_iteration (w : phaseSlice P.phase) :
    (P.iterated m).operator (P.iterationMap m w) = (m : ℝ) • P.iterationMap m (P.operator w) :=
  Subtype.ext (hessian_iterate m N F P.segments.smooth P.short P.nonzero_edges w)

/-- Stable full nullity supplies the genuine iteration equivalence of the
transverse kernels. -/
def kernelEquiv (hnull : nullity F (P.iterated m).point ≤ nullity F P.point) :
    LinearMap.ker P.operator.toLinearMap ≃L[ℝ] LinearMap.ker (P.iterated m).operator.toLinearMap :=
  sliceKernelEquiv (iterL m N) (inner_iterL m N) P.phase P.symmetric (P.iterated m).symmetric
    P.phase_kernel (hessian_iterate m N F P.segments.smooth P.short P.nonzero_edges)
    (iterL_injective m N) P.phase_ne_zero hnull

theorem kernelEquiv_apply (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (w : LinearMap.ker P.operator.toLinearMap) :
    (P.kernelEquiv m hnull w).val = P.iterationMap m w := rfl

/-- The compared functions are the actual transverse polygon energies and
the reduction maps are the same maps used by the splitting construction. -/
theorem reduced_energy_iteration
    (D₀ : ReductionData P.operator P.operator_symmetric P.gradient)
    (D : ReductionData (P.iterated m).operator (P.iterated m).operator_symmetric (P.iterated m).gradient) :
    ∀ᶠ w in 𝓝 (0 : phaseSlice P.phase), P.operator w = 0 →
      (P.iterated m).energy (D.reduction (P.iterationMap m w)) =
        (m : ℝ) ^ 2 * P.energy (D₀.reduction w) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hG : ∀ᶠ w in 𝓝 (0 : phaseSlice P.phase),
      (P.iterated m).gradient (0 + P.iterationMap m w) =
        (m : ℝ) • P.iterationMap m (P.gradient (0 + w)) := by
    simpa only [zero_add] using P.gradient_iteration m
  have hr : ∀ᶠ w in 𝓝 (0 : phaseSlice P.phase),
      kerProj P.operator (D₀.reduction w) = kerProj P.operator w ∧
      cokerProj P.operator (P.gradient (0 + D₀.reduction w)) = cokerProj P.operator w := by
    simpa only [zero_add] using D₀.right_inverse
  have hl : ∀ᶠ z in 𝓝 (0 : phaseSlice (P.iterated m).phase),
      D.reduction (kerProj (P.iterated m).operator z +
        cokerProj (P.iterated m).operator ((P.iterated m).gradient (0 + z))) = z := by
    simpa only [zero_add] using D.left_inverse
  have hf : ∀ᶠ z in 𝓝 (0 : phaseSlice P.phase),
      (P.iterated m).energy (0 + P.iterationMap m z) = (m : ℝ) ^ 2 * P.energy (0 + z) :=
    Eventually.of_forall fun z => by simpa only [zero_add] using P.energy_iteration m z
  simpa only [zero_add] using ReductionNaturality.eventually_reduced_map
    P.operator_symmetric (P.iterated m).operator_symmetric hm (P.operator_iteration m)
    hG D₀.smooth.continuousAt D₀.zero hr hl hf

/-- A strict reduced maximum propagates to every nullity-preserving
iterate. It is a maximum on the transverse kernel, not on the phase orbit. -/
theorem reduced_max_iteration
    (D₀ : ReductionData P.operator P.operator_symmetric P.gradient)
    (D : ReductionData (P.iterated m).operator (P.iterated m).operator_symmetric (P.iterated m).gradient)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hmax : ∀ᶠ (z : LinearMap.ker P.operator.toLinearMap) in 𝓝 0,
      z ≠ 0 → P.energy (D₀.reduction z) < P.energy (D₀.reduction 0)) :
    ∀ᶠ (z : LinearMap.ker (P.iterated m).operator.toLinearMap) in 𝓝 0,
      z ≠ 0 → (P.iterated m).energy (D.reduction z) < (P.iterated m).energy (D.reduction 0) := by
  have hm : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))
  apply strict_max_of_equiv (P.kernelEquiv m hnull) hm _ hmax
  have ht : Tendsto (LinearMap.ker P.operator.toLinearMap).subtypeL (𝓝 0) (𝓝 (0 : phaseSlice P.phase)) := by
    simpa only [map_zero] using (LinearMap.ker P.operator.toLinearMap).subtypeL.continuous.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (P.reduced_energy_iteration m D₀ D)] with z hz
  rw [P.kernelEquiv_apply]
  exact hz z.property

/-- The propagated maximum supplies an actual small maximal disk for the
iterated transverse energy. Orbit and upper-sublevel nonvanishing are not
concluded by this construction. -/
theorem iterated_maximalDisk
    (D₀ : ReductionData P.operator P.operator_symmetric P.gradient)
    (hnull : nullity F (P.iterated m).point ≤ nullity F P.point)
    (hmax : ∀ᶠ (z : LinearMap.ker P.operator.toLinearMap) in 𝓝 0,
      z ≠ 0 → P.energy (D₀.reduction z) < P.energy (D₀.reduction 0)) :
    Nonempty (SurfaceMorseData.MaximalDiskData (P.iterated m).energy 0
      (index F (P.iterated m).point (P.iterated m).symmetric +
        finrank ℝ (LinearMap.ker (P.iterated m).operator.toLinearMap))) := by
  obtain ⟨D⟩ := (P.iterated m).nonempty_reduction
  have h := D.maximalDisk (P.iterated m).operator_symmetric
    (P.iterated m).gradient_smooth (P.iterated m).gradient_derivative (P.iterated m).gradient_zero
    (P.iterated m).energy_derivative (P.reduced_max_iteration m D₀ D hnull hmax)
  simpa only [operator_index] using h

/-- Monodromy gives a single odd arithmetic progression preserving full
nullity for every base iterate. -/
theorem exists_stable_odd_progression (htw : PolygonNullity.Twist F P.point) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ (d : ℕ) [NeZero d] (j : ℕ),
      nullity F ((P.iterated d).iterated (2 * L * j + 1)).point =
        nullity F (P.iterated d).point := by
  obtain ⟨L, hL, _, hper⟩ := PolygonMonodromy.exists_period
    F P.segments.smooth P.short P.nonzero_edges htw
  refine ⟨L, hL, fun d _ j => hper d (2 * L * j + 1) ?_⟩
  have he : d * (2 * L * j + 1) = d + (2 * d * j) * L := by ring
  rw [he, Nat.gcd_add_mul_right_left]

/-- The stable multipliers are odd and occur at bounded forward gaps. -/
theorem odd_progression_bounded_gaps (L : ℕ) (hL : 1 ≤ L) :
    (∀ j : ℕ, Odd (2 * L * j + 1)) ∧
      ∀ t : ℕ, ∃ j : ℕ, t ≤ 2 * L * j + 1 ∧ 2 * L * j + 1 ≤ t + (2 * L + 1) := by
  refine ⟨fun j => ⟨L * j, by ring⟩, fun t => ⟨t / (2 * L) + 1, ?_⟩⟩
  have hpos : 0 < 2 * L := by omega
  have he := Nat.div_add_mod t (2 * L)
  have hr := Nat.mod_lt t hpos
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- A strict transverse reduced maximum at any chosen base iterate
produces actual maximal disks along the monodromy progression. Selecting
a base geodesic with this maximum remains a separate geometric step. -/
theorem exists_stable_odd_maximalDisks (htw : PolygonNullity.Twist F P.point) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ (d : ℕ) [NeZero d]
      (D₀ : ReductionData (P.iterated d).operator (P.iterated d).operator_symmetric
        (P.iterated d).gradient),
      (∀ᶠ (z : LinearMap.ker (P.iterated d).operator.toLinearMap) in 𝓝 0,
        z ≠ 0 → (P.iterated d).energy (D₀.reduction z) < (P.iterated d).energy (D₀.reduction 0)) →
      ∀ j : ℕ, Nonempty (SurfaceMorseData.MaximalDiskData
        ((P.iterated d).iterated (2 * L * j + 1)).energy 0
        (index F ((P.iterated d).iterated (2 * L * j + 1)).point
          ((P.iterated d).iterated (2 * L * j + 1)).symmetric +
          finrank ℝ (LinearMap.ker ((P.iterated d).iterated (2 * L * j + 1)).operator.toLinearMap))) := by
  obtain ⟨L, hL, hper⟩ := P.exists_stable_odd_progression htw
  exact ⟨L, hL, fun d _ D₀ hmax j =>
    (P.iterated d).iterated_maximalDisk (2 * L * j + 1) D₀ (hper d j).le hmax⟩

end PolygonSlice
end Polygon

end
end Finsler.SurfaceIteration
