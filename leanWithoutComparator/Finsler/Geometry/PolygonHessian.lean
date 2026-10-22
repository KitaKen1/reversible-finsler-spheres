module

public import Finsler.Geometry.PolygonChart
public import Finsler.Analysis.Hessian
public import Finsler.Analysis.HessianSplitting
public import Finsler.Analysis.LyapunovSchmidt

/-! The Hessian of the polygon energy in the Hilbert coordinates of a short polygon without zero
edges. The coordinate energy is C³ at the central polygon, so its gradient is C² and its
derivative there, the Hessian, is a symmetric operator on a space of dimension `N * n`. The index
and the nullity are the dimensions of the negative spectral part and of the kernel; their sum is
at most `N * n`. At a stationary polygon the reduction to the kernel applies: all stationary
points of the coordinate energy near the central polygon lie on the image of the kernel under the
reduction map, and along it the derivative of the reduced energy is the inner product with the
gradient, which lies in the kernel. No statement on local cohomology is made here. -/

@[expose] public section

namespace Finsler.PolygonHessian

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart
open Set Filter Module
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n N : ℕ} [NeZero N]

/-- The gradient of the coordinate polygon energy. -/
def grad (F : ReversibleMetric n) (q : ZMod N → Sphere n) : Model n N → Model n N :=
  Hessian.gradient (energy F q)

/-- The Hessian operator of the coordinate polygon energy at the central polygon. -/
def hessian (F : ReversibleMetric n) (q : ZMod N → Sphere n) : Model n N →L[ℝ] Model n N :=
  Hessian.operator (energy F q) (base q)

/-- The nullity of the central polygon: the dimension of the kernel of the Hessian. -/
def nullity (F : ReversibleMetric n) (q : ZMod N → Sphere n) : ℕ :=
  finrank ℝ (LinearMap.ker (hessian F q).toLinearMap)

/-- The index of the central polygon: the dimension of the negative spectral part. -/
def index (F : ReversibleMetric n) (q : ZMod N → Sphere n)
    (hs : (hessian F q).toLinearMap.IsSymmetric) : ℕ :=
  finrank ℝ (HessianSplitting.negative (hessian F q) hs)

theorem finrank_model : finrank ℝ (Model n N) = N * n := by
  have h1 : finrank ℝ (Model n N) = finrank ℝ (ZMod N → Coordinates n) :=
    (WithLp.linearEquiv 2 ℝ (ZMod N → Coordinates n)).finrank_eq
  rw [h1, Module.finrank_pi_fintype]
  simp [ZMod.card]

theorem index_add_nullity_le (F : ReversibleMetric n) (q : ZMod N → Sphere n)
    (hs : (hessian F q).toLinearMap.IsSymmetric) : index F q hs + nullity F q ≤ N * n := by
  have h := HessianSplitting.finrank_three_parts (hessian F q) hs
  rw [finrank_model] at h
  unfold index nullity
  omega

/-- The index counts the negative eigenvalues of the Hessian with multiplicity. -/
theorem index_eq_ncard (F : ReversibleMetric n) (q : ZMod N → Sphere n)
    (hs : (hessian F q).toLinearMap.IsSymmetric) :
    index F q hs = {i | hs.eigenvalues rfl i < 0}.ncard :=
  HessianSplitting.finrank_negative (hessian F q) hs

/-- The nullity counts the zero eigenvalues of the Hessian with multiplicity. -/
theorem nullity_eq_ncard (F : ReversibleMetric n) (q : ZMod N → Sphere n)
    (hs : (hessian F q).toLinearMap.IsSymmetric) :
    nullity F q = {i | hs.eigenvalues rfl i = 0}.ncard :=
  HessianSplitting.finrank_ker (hessian F q) hs

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne

/-- The Hessian at a short polygon without zero edges is symmetric. -/
theorem hessian_isSymmetric : (hessian F q).toLinearMap.IsSymmetric :=
  Hessian.operator_isSymmetric ((energy_contDiffAt F hδ hq hne).of_le (by norm_num))

/-- The Hessian is the derivative of the gradient. -/
theorem grad_hasFDerivAt : HasFDerivAt (grad F q) (hessian F q) (base q) :=
  Hessian.gradient_hasFDerivAt ((energy_contDiffAt F hδ hq hne).of_le (by norm_num))

theorem grad_contDiffAt : ContDiffAt ℝ 2 (grad F q) (base q) :=
  Hessian.gradient_contDiffAt (energy_contDiffAt F hδ hq hne)

/-- Near the central polygon the coordinate energy is differentiable with the gradient as the
representative of its derivative. -/
theorem eventually_hasFDerivAt :
    ∀ᶠ x in 𝓝 (base q), HasFDerivAt (energy F q) (innerSL ℝ (grad F q x)) x := by
  have hE := energy_contDiffAt F hδ hq hne
  refine (hE.eventually (by simp)).mono fun x hx => ?_
  have hd : HasFDerivAt (energy F q) (fderiv ℝ (energy F q) x) x :=
    (hx.differentiableAt (by simp)).hasFDerivAt
  have he : fderiv ℝ (energy F q) x = innerSL ℝ (grad F q x) :=
    ContinuousLinearMap.ext fun v => (Hessian.inner_gradient (energy F q) x v).symm
  rwa [he] at hd

/-- The gradient vanishes at a stationary polygon. -/
theorem grad_eq_zero_of_polyCritical (hc : PolyCritical F N q) : grad F q (base q) = 0 :=
  (Hessian.gradient_eq_zero_iff _ _).mpr (fderiv_energy_eq_zero_of_polyCritical F hδ hq hne hc)

/-- Reduction to the kernel of the Hessian at a stationary short polygon without zero edges. -/
theorem exists_reduction (hc : PolyCritical F N q) :
    ∃ σ : Model n N → Model n N, ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0 : Model n N), hessian F q w = 0 →
        LyapunovSchmidt.kerProj (hessian F q) (σ w) = w ∧
          hessian F q (grad F q (base q + σ w)) = 0) ∧
      (∀ᶠ z in 𝓝 (0 : Model n N), hessian F q (grad F q (base q + z)) = 0 →
        σ (LyapunovSchmidt.kerProj (hessian F q) z) = z) ∧
      ∀ᶠ w in 𝓝 (0 : Model n N), hessian F q w = 0 →
        HasFDerivAt (fun w => energy F q (base q + σ w))
          ((innerSL ℝ (grad F q (base q + σ w))).comp
            (LyapunovSchmidt.kerProj (hessian F q))) w :=
  LyapunovSchmidt.exists_reduced_function (hessian_isSymmetric F hδ hq hne) (by norm_num)
    (grad_contDiffAt F hδ hq hne) (grad_hasFDerivAt F hδ hq hne)
    (grad_eq_zero_of_polyCritical F hδ hq hne hc) (eventually_hasFDerivAt F hδ hq hne)

/-- Stationary points of the coordinate energy near a stationary central polygon lie on the
image of the kernel of the Hessian under the reduction map. -/
theorem exists_reduction_zeros (hc : PolyCritical F N q) :
    ∃ σ : Model n N → Model n N, ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧
      ∀ᶠ z in 𝓝 (0 : Model n N), grad F q (base q + z) = 0 →
        ∃ w, hessian F q w = 0 ∧ σ w = z := by
  obtain ⟨σ, hσ, hσ0, -, hz, -⟩ := exists_reduction F hδ hq hne hc
  refine ⟨σ, hσ, hσ0, hz.mono fun z hz hg => ?_⟩
  refine ⟨LyapunovSchmidt.kerProj (hessian F q) z, LyapunovSchmidt.map_kerProj _ z, hz ?_⟩
  rw [hg, map_zero]

end Regular

end

end Finsler.PolygonHessian
