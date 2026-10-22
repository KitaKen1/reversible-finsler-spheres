module

public import Finsler.Analysis.IntervalH1VelocityContinuity
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! C^∞ regularity of actual positive-energy tangent-critical H¹ sphere loops on (0,1).
The metric's fiber Hessian is transferred to the ambient velocity Hessian, which is
positive on tangent directions. The tangent Legendre covector, made invertible in the
radial velocity direction and read in coordinates, is a smooth map with injective
derivative at every unit position with nonzero tangent velocity; mathlib's inverse
function theorem gives a C^∞ local inverse. Along the C¹ representative the recovered
covector is a finite sum of momentum primitives of a continuous force, so a
Hamiltonian-type induction lifts C^k to C^(k+1). Smoothness across the periodic
endpoint, readback as an ordinary smooth closed geodesic and realization of every
tangent direction remain separate. -/

@[expose] public section

namespace Finsler.SobolevSmoothRegularity

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.AmbientLagrangian Finsler.FiberEnergy Finsler.FiberLegendre
open Finsler.SobolevRotationalRecovery Finsler.SobolevVelocityContinuity
open Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ### Part A: the velocity Hessian on tangent vectors -/

theorem fiber_mem_slitDomain (x : Sphere n) {w : Model n} (hw : w ≠ 0) :
    ((x : Ambient n), ambientMap x w) ∈ slitDomain n := by
  refine ⟨ne_zero_of_mem_unit_sphere x, ?_⟩
  change lift (ambientPair ⟨x, w⟩) ∈ slitBundle n
  rw [lift_ambientPair]
  exact hw

theorem line_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w k : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => w + r • k) k s := by
  have h := ((hasDerivAt_id' s).smul_const k).const_add w
  rwa [one_smul] at h

/-- Derivative of the velocity differential along a velocity line, evaluated in a fixed
direction. -/
theorem velocityDifferential_line_hasDerivAt (F : ReversibleMetric n)
    {z : Ambient n × Ambient n} (hz : z ∈ slitDomain n) (h u : Ambient n) :
    HasDerivAt (fun r : ℝ => fderiv ℝ (lagrangian F) (z.1, z.2 + r • h) ((0 : Ambient n), u))
      (fderiv ℝ (fderiv ℝ (lagrangian F)) z ((0 : Ambient n), h) ((0 : Ambient n), u)) 0 := by
  have hsmooth := lagrangian_smoothAt F hz
  have hdL : DifferentiableAt ℝ (fderiv ℝ (lagrangian F)) z :=
    (hsmooth.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpath : HasDerivAt (fun r : ℝ => (z.1, z.2 + r • h)) ((0 : Ambient n), h) 0 :=
    (hasDerivAt_const (0 : ℝ) z.1).prodMk (line_hasDerivAt z.2 h 0)
  have h1 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdL.hasFDerivAt hpath
    (by simp only [zero_smul, add_zero])
  have h2 := (ContinuousLinearMap.apply ℝ ℝ ((0 : Ambient n), u)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) h1
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h2

/-- The ambient velocity Hessian on fiber vectors is twice the metric's fiber Hessian. -/
theorem lagrangian_hessian_fiber (F : ReversibleMetric n) (x : Sphere n) {w : Model n}
    (hw : w ≠ 0) (k : Model n) :
    fderiv ℝ (fderiv ℝ (lagrangian F)) ((x : Ambient n), ambientMap x w)
        ((0 : Ambient n), ambientMap x k) ((0 : Ambient n), ambientMap x k) =
      2 * fderiv ℝ (fderiv ℝ (halfSquared F x)) w k k := by
  let D : Model n →L[ℝ] Ambient n := ambientMap x
  have hL := velocityDifferential_line_hasDerivAt F (z := ((x : Ambient n), D w))
    (fiber_mem_slitDomain x hw) (D k) (D k)
  have hdH : DifferentiableAt ℝ (fderiv ℝ (halfSquared F x)) w :=
    ((halfSquared_smoothAt F x hw).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hH1 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdH.hasFDerivAt (line_hasDerivAt w k 0)
    (by simp only [zero_smul, add_zero])
  have hH2 := ((ContinuousLinearMap.apply ℝ ℝ k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hH1).const_mul
    (2 : ℝ)
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hH2
  have heq : (fun r : ℝ => fderiv ℝ (lagrangian F)
      (((x : Ambient n), D w).1, ((x : Ambient n), D w).2 + r • D k) ((0 : Ambient n), D k)) =
      fun r => 2 * fderiv ℝ (halfSquared F x) (w + r • k) k := by
    funext r
    have hlin : D w + r • D k = D (w + r • k) := by rw [D.map_add, D.map_smul]
    have h := velocityDifferential_fiber F x (w + r • k) k
    change fderiv ℝ (lagrangian F) ((x : Ambient n), D w + r • D k) ((0 : Ambient n), D k) = _
    rw [hlin]
    exact h
  rw [heq] at hL
  exact hL.unique hH2

theorem lagrangian_hessian_tangent_pos (F : ReversibleMetric n) {q v h : Ambient n}
    (hq : ‖q‖ = 1) (hv : ⟪q, v⟫ = 0) (hv0 : v ≠ 0) (hh : ⟪q, h⟫ = 0) (hh0 : h ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (lagrangian F)) (q, v) ((0 : Ambient n), h) ((0 : Ambient n), h) := by
  let x : Sphere n := ⟨q, by simpa using hq⟩
  obtain ⟨w, rfl⟩ := exists_fiber_of_orthogonal x hv
  obtain ⟨k, rfl⟩ := exists_fiber_of_orthogonal x hh
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv0 (ambientMap x).map_zero
  have hk : k ≠ 0 := by
    rintro rfl
    exact hh0 (ambientMap x).map_zero
  change 0 < fderiv ℝ (fderiv ℝ (lagrangian F)) ((x : Ambient n), ambientMap x w)
    ((0 : Ambient n), ambientMap x k) ((0 : Ambient n), ambientMap x k)
  rw [lagrangian_hessian_fiber F x hw k]
  have := halfSquared_hessian_pos F x hw hk
  linarith

/-! ### Part B: the extended tangent Legendre map -/

theorem tangent_mem_slitDomain {q v : Ambient n} (hq : ‖q‖ = 1) (hv : ⟪q, v⟫ = 0)
    (hv0 : v ≠ 0) : (q, v) ∈ slitDomain n := by
  let x : Sphere n := ⟨q, by simpa using hq⟩
  obtain ⟨w, rfl⟩ := exists_fiber_of_orthogonal x hv
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv0 (ambientMap x).map_zero
  exact fiber_mem_slitDomain x hw

/-- Coordinates of a covector in the standard orthonormal basis, as an ambient vector. -/
def covectorVectorL (n : ℕ) : (Ambient n →L[ℝ] ℝ) →L[ℝ] Ambient n :=
  ∑ i, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)).smulRight
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i : Ambient n)

theorem inner_covectorVectorL (p : Ambient n →L[ℝ] ℝ) (u : Ambient n) :
    ⟪u, covectorVectorL n p⟫ = p u := by
  have hu : (∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i, u⟫ •
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i : Ambient n)) = u :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr' u
  conv_rhs => rw [← hu]
  simp only [covectorVectorL, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.apply_apply, inner_sum, real_inner_smul_right, map_sum, map_smul,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i) u, mul_comm]

/-- The tangent Legendre covector, made invertible in the radial velocity direction. -/
def legendreExt (F : ReversibleMetric n) (z : Ambient n × Ambient n) : Ambient n × Ambient n :=
  (z.1, covectorVectorL n (tangentCovector z.1 (velocityDifferential F z)) + ⟪z.1, z.2⟫ • z.1)

theorem legendreExt_contDiffAt (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z ∈ slitDomain n) : ContDiffAt ℝ ∞ (legendreExt F) z := by
  have hL := lagrangian_smoothAt F hz
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (lagrangian F)) z := hL.fderiv_right (m := ∞) (by simp)
  have hvd : ContDiffAt ℝ ∞ (velocityDifferential F) z := by
    show ContDiffAt ℝ ∞ (fun y : Ambient n × Ambient n => (fderiv ℝ (lagrangian F) y).comp
      (ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n))) z
    exact hfd.clm_comp contDiffAt_const
  have hq : ContDiffAt ℝ ∞ (fun y : Ambient n × Ambient n => y.1) z := contDiffAt_fst
  have hw : ContDiffAt ℝ ∞ (fun y : Ambient n × Ambient n => y.2) z := contDiffAt_snd
  have htc : ContDiffAt ℝ ∞
      (fun y : Ambient n × Ambient n => tangentCovector y.1 (velocityDifferential F y)) z := by
    show ContDiffAt ℝ ∞ (fun y : Ambient n × Ambient n =>
      velocityDifferential F y - velocityDifferential F y y.1 • innerSL ℝ y.1) z
    exact hvd.sub ((hvd.clm_apply hq).smul ((innerSL ℝ).contDiff.contDiffAt.comp z hq))
  exact hq.prodMk (((covectorVectorL n).contDiff.contDiffAt.comp z htc).add
    ((hq.inner ℝ hw).smul hq))

theorem legendreExt_fst (F : ReversibleMetric n) (z : Ambient n × Ambient n) :
    (legendreExt F z).1 = z.1 := rfl

theorem inner_legendreExt_snd (F : ReversibleMetric n) (z : Ambient n × Ambient n)
    (u : Ambient n) :
    ⟪u, (legendreExt F z).2⟫ = velocityDifferential F z u -
      velocityDifferential F z z.1 * ⟪z.1, u⟫ + ⟪z.1, z.2⟫ * ⟪u, z.1⟫ := by
  simp only [legendreExt, inner_add_right, inner_covectorVectorL, real_inner_smul_right,
    tangentCovector_apply]

theorem legendreExt_fderiv_injective (F : ReversibleMetric n) {q v : Ambient n}
    (hq : ‖q‖ = 1) (hv : ⟪q, v⟫ = 0) (hv0 : v ≠ 0) :
    Function.Injective (fderiv ℝ (legendreExt F) (q, v)) := by
  have hz := tangent_mem_slitDomain hq hv hv0
  have hD := ((legendreExt_contDiffAt F hz).differentiableAt (by simp)).hasFDerivAt
  set D := fderiv ℝ (legendreExt F) (q, v) with hDdef
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, h⟩ hzero
  -- first component
  have hfst : (ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).comp D =
      ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n) := by
    have h1 := (ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).hasFDerivAt.comp (q, v) hD
    exact h1.unique (hasFDerivAt_fst (p := (q, v)))
  have ha : a = 0 := by
    have := congrArg (fun L : (Ambient n × Ambient n) →L[ℝ] Ambient n => L (a, h)) hfst
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', hzero,
      Prod.fst_zero] at this
    exact this.symm
  subst ha
  -- second component along the velocity line
  have hpath : HasDerivAt (fun r : ℝ => (q, v + r • h)) ((0 : Ambient n), h) 0 :=
    (hasDerivAt_const (0 : ℝ) q).prodMk (line_hasDerivAt v h 0)
  have hline (u : Ambient n) : ⟪u, (D ((0 : Ambient n), h)).2⟫ =
      fderiv ℝ (fderiv ℝ (lagrangian F)) (q, v) ((0 : Ambient n), h) ((0 : Ambient n), u) -
        fderiv ℝ (fderiv ℝ (lagrangian F)) (q, v) ((0 : Ambient n), h) ((0 : Ambient n), q) *
          ⟪q, u⟫ + ⟪q, h⟫ * ⟪u, q⟫ := by
    have hφ := ((innerSL ℝ u).comp (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n))).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hD hpath (by simp only [zero_smul, add_zero]))
    have hA := velocityDifferential_line_hasDerivAt F hz h u
    have hB := velocityDifferential_line_hasDerivAt F hz h q
    have hlin : HasDerivAt (fun r : ℝ => (⟪q, v⟫ + r * ⟪q, h⟫) * ⟪u, q⟫) (⟪q, h⟫ * ⟪u, q⟫) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).mul_const ⟪q, h⟫).const_add ⟪q, v⟫
      simpa only [one_mul] using this.mul_const ⟪u, q⟫
    have hsum := (hA.sub (hB.mul_const ⟪q, u⟫)).add hlin
    have hfun : (⇑((innerSL ℝ u).comp (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n))) ∘
        legendreExt F ∘ fun r : ℝ => (q, v + r • h)) =
        ((fun r : ℝ => fderiv ℝ (lagrangian F) ((q, v).1, (q, v).2 + r • h) ((0 : Ambient n), u)) -
          fun r : ℝ => fderiv ℝ (lagrangian F) ((q, v).1, (q, v).2 + r • h)
            ((0 : Ambient n), q) * ⟪q, u⟫) +
          fun r : ℝ => (⟪q, v⟫ + r * ⟪q, h⟫) * ⟪u, q⟫ := by
      funext r
      simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_snd', innerSL_apply_apply]
      rw [inner_legendreExt_snd]
      simp only [velocityDifferential, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply, inner_add_right, real_inner_smul_right]
    rw [hfun] at hφ
    have huniq := hφ.unique hsum
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      innerSL_apply_apply] using huniq
  have h2 : (D ((0 : Ambient n), h)).2 = 0 := by rw [hzero]; rfl
  have hqh : ⟪q, h⟫ = 0 := by
    have h3 := hline q
    rw [h2, inner_zero_right, real_inner_self_eq_norm_sq, hq] at h3
    linarith
  by_contra hne
  have hh0 : h ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
  have h4 := hline h
  rw [h2, inner_zero_right, hqh, real_inner_comm q h, hqh] at h4
  simp only [mul_zero, sub_zero, add_zero] at h4
  have hpos := lagrangian_hessian_tangent_pos F hq hv hv0 hqh hh0
  linarith

/-! ### Part C: smooth local inverse -/

theorem exists_smooth_local_inverse (F : ReversibleMetric n) {q v : Ambient n}
    (hq : ‖q‖ = 1) (hv : ⟪q, v⟫ = 0) (hv0 : v ≠ 0) :
    ∃ g : Ambient n × Ambient n → Ambient n × Ambient n,
      ContDiffAt ℝ ∞ g (legendreExt F (q, v)) ∧
        ∀ᶠ z in 𝓝 (q, v), g (legendreExt F z) = z := by
  have hz := tangent_mem_slitDomain hq hv hv0
  have hC := legendreExt_contDiffAt F hz
  have hD := (hC.differentiableAt (by simp)).hasFDerivAt
  let e : (Ambient n × Ambient n) ≃L[ℝ] (Ambient n × Ambient n) :=
    (LinearEquiv.ofInjectiveEndo
      ((fderiv ℝ (legendreExt F) (q, v) : (Ambient n × Ambient n) →L[ℝ] _) :
        (Ambient n × Ambient n) →ₗ[ℝ] _)
      (legendreExt_fderiv_injective F hq hv hv0)).toContinuousLinearEquiv
  have he : (e : (Ambient n × Ambient n) →L[ℝ] (Ambient n × Ambient n)) =
      fderiv ℝ (legendreExt F) (q, v) := by
    exact ContinuousLinearMap.ext fun x => rfl
  have hD' : HasFDerivAt (legendreExt F)
      (e : (Ambient n × Ambient n) →L[ℝ] (Ambient n × Ambient n)) (q, v) := by
    rw [he]
    exact hD
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := ContDiffAt.hasStrictFDerivAt' hC hD' hn
  let φ := hstrict.toOpenPartialHomeomorph (legendreExt F)
  have hsrc : (q, v) ∈ φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have htgt : legendreExt F (q, v) ∈ φ.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hsymm : φ.symm (legendreExt F (q, v)) = (q, v) := φ.left_inv hsrc
  refine ⟨φ.symm, ?_, φ.eventually_left_inverse hsrc⟩
  apply φ.contDiffAt_symm htgt
  · rw [hsymm]
    exact hD'
  · rw [hsymm]
    exact hC

/-! ### Part D: bootstrap of positive tangent-critical loops to C^∞ -/

section Bootstrap

open MeasureTheory Finsler.IntervalSobolev Finsler.SobolevRotationalVariation
open Finsler.SobolevRotationalBounds Finsler.SobolevZeroExclusion Finsler.SobolevCurveVariation
open Finsler.SobolevEnergyDifferential Finsler.SobolevEnergy
open scoped Interval

variable {ι : Type*} [Fintype ι]

theorem contDiffAt_succ_of_hasDerivAt {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {f f' : ℝ → F'} {x : ℝ} {k : ℕ} (hd : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y)
    (hk : ContDiffAt ℝ k f' x) : ContDiffAt ℝ (k + 1) f x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f' y), ?_, ?_⟩
  · obtain ⟨u, hu, hmem⟩ := hd.exists_mem
    exact ⟨u, hu, fun y hy => (hmem y hy).hasFDerivAt⟩
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ F' (1 : ℝ →L[ℝ] ℝ)).contDiff.contDiffAt.comp x hk

/-- The force along the continuous jet (q, v) of the C¹ representative. -/
def smoothForce (F : ReversibleMetric n) (q v : ℝ → Ambient n)
    (A : Ambient n →L[ℝ] Ambient n) (t : ℝ) : ℝ :=
  fderiv ℝ (lagrangian F) (q t, v t) (A (q t), A (v t))

variable (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n) (u : SphereLoop n)
  (hc : TangentCritical F u)

/-- Abbreviations for the representative, velocity and covector. -/
local notation "qR" => continuousRepresentative (u.data : Space n)
local notation "vR" => velocityRep b F u hc
local notation "QR" => recoveredCovector b F u hc

theorem legendreExt_path {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    legendreExt F (qR t, vR t) = (qR t, covectorVectorL n (QR t)) := by
  have hspec := (velocityRep_spec b F u hc ht).2
  have htan := velocityRep_tangent b F u hc ht
  refine Prod.ext rfl ?_
  change covectorVectorL n (tangentCovector (qR t) (velocityDifferential F (qR t, vR t))) +
    ⟪qR t, vR t⟫ • qR t = covectorVectorL n (QR t)
  rw [htan, zero_smul, add_zero]
  exact congrArg (covectorVectorL n) hspec

theorem path_mem_slitDomain (hE : 0 < energy F u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (qR t, vR t) ∈ slitDomain n :=
  tangent_mem_slitDomain (u.sphere_constraint ⟨t, ht⟩) (velocityRep_tangent b F u hc ht)
    (velocityRep_ne_zero b F u hc hE ht)

theorem force_ae_smoothForce (A : Ambient n →L[ℝ] Ambient n) :
    force F u A =ᵐ[intervalMeasure] smoothForce F qR vR A := by
  filter_upwards [velocityRep_ae b F u hc] with t ht
  unfold force smoothForce
  rw [differential_split]
  change positionDifferential F (qR t, velocity (u.data : Space n) t) (A (qR t)) +
      velocityDifferential F (qR t, velocity (u.data : Space n) t)
        (A (velocity (u.data : Space n) t)) =
    positionDifferential F (qR t, vR t) (A (qR t)) + velocityDifferential F (qR t, vR t) (A (vR t))
  rw [ht]

theorem momentum_sub_smoothForce {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    momentumRepresentative F u hA hc t - momentumRepresentative F u hA hc s =
      ∫ x in s..t, smoothForce F qR vR A x := by
  rw [momentumRepresentative_sub F u hA hc hs ht]
  apply intervalIntegral.integral_congr_ae
  have h1 := force_ae_smoothForce b F u hc A
  change ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at h1
  rw [restrict_Ioo_eq_restrict_Icc] at h1
  have hsub : Ι s t ⊆ Icc 0 1 := by
    intro x hx
    rcases le_total s t with hst | hst
    · rw [uIoc_of_le hst] at hx
      exact ⟨hs.1.trans hx.1.le, hx.2.trans ht.2⟩
    · rw [uIoc_of_ge hst] at hx
      exact ⟨ht.1.trans hx.1.le, hx.2.trans hs.2⟩
  have h2 := ae_restrict_of_ae_restrict_of_subset hsub h1
  filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp h2] with x hx hxI
  exact hx hxI

theorem smoothForce_contDiffAt (hE : 0 < energy F u) (A : Ambient n →L[ℝ] Ambient n) {k : ℕ}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hq : ContDiffAt ℝ k qR t) (hv : ContDiffAt ℝ k vR t) :
    ContDiffAt ℝ k (smoothForce F qR vR A) t := by
  have hL := lagrangian_smoothAt F (path_mem_slitDomain b F u hc hE ht)
  have hfd : ContDiffAt ℝ k (fderiv ℝ (lagrangian F)) (qR t, vR t) :=
    hL.fderiv_right (m := k) (by exact_mod_cast le_top)
  have hpair : ContDiffAt ℝ k (fun s => (qR s, vR s)) t := hq.prodMk hv
  have hdir : ContDiffAt ℝ k (fun s => (A (qR s), A (vR s))) t :=
    (A.contDiff.contDiffAt.comp t hq).prodMk (A.contDiff.contDiffAt.comp t hv)
  exact (hfd.comp t hpair).clm_apply hdir

theorem momentum_contDiffAt {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) {k : ℕ}
    (hforce : ∀ t ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ k (smoothForce F qR vR A) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ (k + 1) (momentumRepresentative F u hA hc) t₀ := by
  have hcont : ContinuousOn (smoothForce F qR vR A) (Ioo 0 1) := fun t ht =>
    (hforce t ht).continuousAt.continuousWithinAt
  have hderiv (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (momentumRepresentative F u hA hc) (smoothForce F qR vR A y) y := by
    have hG : HasDerivAt (fun z => momentumRepresentative F u hA hc y +
        ∫ x in y..z, smoothForce F qR vR A x) (smoothForce F qR vR A y) y :=
      (intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl)
        (hcont.stronglyMeasurableAtFilter isOpen_Ioo y hy)
        (hforce y hy).continuousAt).const_add _
    apply hG.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    rw [← momentum_sub_smoothForce b F u hc hA (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hz)]
    ring
  exact contDiffAt_succ_of_hasDerivAt
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht₀) hderiv) (hforce t₀ ht₀)

theorem recoveredCovector_contDiffAt {k : ℕ} {t₀ : ℝ} (hq : ContDiffAt ℝ k qR t₀)
    (hP : ∀ i j, ContDiffAt ℝ k
      (momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc) t₀) :
    ContDiffAt ℝ k QR t₀ := by
  classical
  unfold recoveredCovector
  apply ContDiffAt.sum
  intro i _
  exact (ContDiffAt.sum fun j _ => (contDiffAt_const.inner ℝ hq).mul (hP i j)).smul
    contDiffAt_const

theorem velocityRep_eventually_inverse (hE : 0 < energy F u) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ g : Ambient n × Ambient n → Ambient n × Ambient n,
      ContDiffAt ℝ ∞ g (qR t₀, covectorVectorL n (QR t₀)) ∧
        vR =ᶠ[𝓝 t₀] fun t => (g (qR t, covectorVectorL n (QR t))).2 := by
  have ht₀' := Ioo_subset_Icc_self ht₀
  obtain ⟨g, hg, hinv⟩ := exists_smooth_local_inverse F (u.sphere_constraint ⟨t₀, ht₀'⟩)
    (velocityRep_tangent b F u hc ht₀') (velocityRep_ne_zero b F u hc hE ht₀')
  refine ⟨g, ?_, ?_⟩
  · rw [← legendreExt_path b F u hc ht₀']
    exact hg
  · have hqc : ContinuousAt qR t₀ :=
      (representative_hasDerivAt b F u hc ht₀).continuousAt
    have hpath : ContinuousAt (fun t => (qR t, vR t)) t₀ :=
      hqc.prodMk (velocityRep_continuous b F u hc).continuousAt
    filter_upwards [hpath.eventually hinv, isOpen_Ioo.mem_nhds ht₀] with t ht hmem
    rw [← legendreExt_path b F u hc (Ioo_subset_Icc_self hmem), ht]

/-- C^∞ bootstrap on the open interval. -/
theorem velocityRep_contDiffAt_nat (hE : 0 < energy F u) (k : ℕ) :
    ∀ t ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ k vR t := by
  induction k with
  | zero =>
    intro t _
    exact contDiffAt_zero.mpr ⟨univ, univ_mem, (velocityRep_continuous b F u hc).continuousOn⟩
  | succ k ih =>
    intro t₀ ht₀
    have hqd (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : HasDerivAt qR (vR y) y :=
      representative_hasDerivAt b F u hc hy
    have hq1 (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : ContDiffAt ℝ (k + 1) qR y :=
      contDiffAt_succ_of_hasDerivAt (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) hqd)
        (ih y hy)
    have hforce (A : Ambient n →L[ℝ] Ambient n) :
        ∀ t ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ k (smoothForce F qR vR A) t := fun t ht =>
      smoothForce_contDiffAt b F u hc hE A (Ioo_subset_Icc_self ht)
        ((hq1 t ht).of_le (by exact_mod_cast Nat.le_succ k)) (ih t ht)
    have hP (i j : ι) : ContDiffAt ℝ (k + 1)
        (momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc) t₀ :=
      momentum_contDiffAt b F u hc (planeRotation_isRotation (b i) (b j))
        (hforce _) ht₀
    have hQ : ContDiffAt ℝ (k + 1) QR t₀ :=
      recoveredCovector_contDiffAt b F u hc (hq1 t₀ ht₀) hP
    obtain ⟨g, hg, hev⟩ := velocityRep_eventually_inverse b F u hc hE ht₀
    have hcomp : ContDiffAt ℝ (k + 1) (fun t => (g (qR t, covectorVectorL n (QR t))).2) t₀ := by
      have hpath : ContDiffAt ℝ (k + 1) (fun t => (qR t, covectorVectorL n (QR t))) t₀ :=
        (hq1 t₀ ht₀).prodMk ((covectorVectorL n).contDiff.contDiffAt.comp t₀ hQ)
      exact contDiffAt_snd.comp t₀ ((hg.of_le (by exact_mod_cast le_top)).comp t₀ hpath)
    have h := hcomp.congr_of_eventuallyEq hev
    exact_mod_cast h

theorem velocityRep_contDiffAt (hE : 0 < energy F u) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ vR t :=
  contDiffAt_infty.mpr fun k => velocityRep_contDiffAt_nat b F u hc hE k t ht

end Bootstrap

/-- Positive-energy tangent-critical actual H¹ loops are C^∞ on the open interval. -/
theorem representative_contDiffAt (F : ReversibleMetric n) (u : Finsler.IntervalSobolev.SphereLoop n)
    (hc : Finsler.SobolevCurveVariation.TangentCritical F u) (hE : 0 < Finsler.SobolevEnergy.energy F u) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (Finsler.IntervalSobolev.continuousRepresentative
      (u.data : Finsler.IntervalSobolev.Space n)) t := by
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  apply contDiffAt_infty.mpr
  intro k
  have hd : ∀ᶠ y in 𝓝 t, HasDerivAt (Finsler.IntervalSobolev.continuousRepresentative
      (u.data : Finsler.IntervalSobolev.Space n)) (velocityRep b F u hc y) y :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun y hy =>
      representative_hasDerivAt b F u hc hy
  have hv : ContDiffAt ℝ k (velocityRep b F u hc) t :=
    (velocityRep_contDiffAt b F u hc hE ht).of_le (by exact_mod_cast le_top)
  exact (contDiffAt_succ_of_hasDerivAt hd hv).of_le (by exact_mod_cast Nat.le_succ k)

end

end Finsler.SobolevSmoothRegularity
