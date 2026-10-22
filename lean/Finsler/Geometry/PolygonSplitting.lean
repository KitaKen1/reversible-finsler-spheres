module

public import Finsler.Geometry.PolygonHessian
public import Finsler.Analysis.SplittingLemma

/-! The degenerate splitting lemma for the polygon energy. At a stationary short polygon without
zero edges, in the Hilbert coordinates of the polygon, the coordinate energy is the sum of the
reduced energy on the kernel of the Hessian and the quadratic form of the Hessian, in a chart
that is `C¹`, tangent to the identity and preserves the kernel coordinate. If the Hessian is
injective, the coordinate energy is its value at the polygon plus the quadratic form of the
Hessian in such a chart. No statement on local cohomology is made here. -/

@[expose] public section

namespace Finsler.PolygonSplitting

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.LyapunovSchmidt
open Set Filter Module
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n N : ℕ} [NeZero N] (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne

/-- The splitting of the coordinate polygon energy at a stationary short polygon without zero
edges. -/
theorem exists_splitting (hc : PolyCritical F N q) :
    ∃ σ Ξ : Model n N → Model n N, ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0 : Model n N), hessian F q w = 0 →
        kerProj (hessian F q) (σ w) = w ∧ hessian F q (grad F q (base q + σ w)) = 0) ∧
      (∀ᶠ z in 𝓝 (0 : Model n N), hessian F q (grad F q (base q + z)) = 0 →
        σ (kerProj (hessian F q) z) = z) ∧
      (∀ᶠ w in 𝓝 (0 : Model n N), hessian F q w = 0 →
        HasFDerivAt (fun w => energy F q (base q + σ w))
          ((innerSL ℝ (grad F q (base q + σ w))).comp (kerProj (hessian F q))) w) ∧
      ContDiffAt ℝ 1 Ξ 0 ∧ Ξ 0 = 0 ∧
      HasStrictFDerivAt Ξ (ContinuousLinearMap.id ℝ (Model n N)) 0 ∧
      (∀ᶠ z in 𝓝 (0 : Model n N), kerProj (hessian F q) (Ξ z) = kerProj (hessian F q) z) ∧
      ∀ᶠ z in 𝓝 (0 : Model n N), energy F q (base q + z) =
        energy F q (base q + σ (kerProj (hessian F q) z)) +
          1 / 2 * ⟪hessian F q (Ξ z), Ξ z⟫ :=
  SplittingLemma.exists_splitting (hessian_isSymmetric F hδ hq hne)
    (grad_contDiffAt F hδ hq hne) (grad_hasFDerivAt F hδ hq hne)
    (grad_eq_zero_of_polyCritical F hδ hq hne hc) (eventually_hasFDerivAt F hδ hq hne)

/-- The Morse lemma for the coordinate polygon energy at a stationary short polygon without zero
edges whose Hessian is injective. -/
theorem exists_morse (hc : PolyCritical F N q) (hinj : ∀ w, hessian F q w = 0 → w = 0) :
    ∃ Ξ : Model n N → Model n N, ContDiffAt ℝ 1 Ξ 0 ∧ Ξ 0 = 0 ∧
      HasStrictFDerivAt Ξ (ContinuousLinearMap.id ℝ (Model n N)) 0 ∧
      ∀ᶠ z in 𝓝 (0 : Model n N), energy F q (base q + z) =
        energy F q (base q) + 1 / 2 * ⟪hessian F q (Ξ z), Ξ z⟫ :=
  SplittingLemma.exists_morse (hessian_isSymmetric F hδ hq hne)
    (grad_contDiffAt F hδ hq hne) (grad_hasFDerivAt F hδ hq hne)
    (grad_eq_zero_of_polyCritical F hδ hq hne hc) (eventually_hasFDerivAt F hδ hq hne) hinj

/-- The splitting of the coordinate polygon energy as a local homeomorphism. -/
theorem exists_homeomorph (hc : PolyCritical F N q) :
    ∃ (σ : Model n N → Model n N) (e : OpenPartialHomeomorph (Model n N) (Model n N)),
      ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧ (0 : Model n N) ∈ e.source ∧ e 0 = 0 ∧
      ∀ z ∈ e.source, kerProj (hessian F q) (e z) = kerProj (hessian F q) z ∧
        energy F q (base q + z) =
          energy F q (base q + σ (kerProj (hessian F q) z)) +
            1 / 2 * ⟪hessian F q (e z), e z⟫ :=
  SplittingLemma.exists_homeomorph (hessian_isSymmetric F hδ hq hne)
    (grad_contDiffAt F hδ hq hne) (grad_hasFDerivAt F hδ hq hne)
    (grad_eq_zero_of_polyCritical F hδ hq hne hc) (eventually_hasFDerivAt F hδ hq hne)

end

end Finsler.PolygonSplitting
