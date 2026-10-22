module

public import Finsler.Geometry.PolygonIterate
public import Finsler.Geometry.PolygonHessian
public import Finsler.Analysis.ReductionNaturality

/-! The reduction to the kernel for an iterated polygon. For a stationary short polygon `q`
without zero edges and its `m`-fold iterate, in the Hilbert coordinates: the gradient of the
coordinate energy of the iterate at an iterated point is `m` times the iterated gradient
(symmetric criticality for the rotation by one period, and the scaling `m²` of the energy and
`m` of the inner product); the Hessian of the iterate on iterated vectors is `m` times the
iterated Hessian; the nullity does not decrease; reduction maps of `q` and of its iterate are
intertwined by the iteration map on the kernel, and the reduced energy of the iterate at an
iterated kernel vector is `m²` times the reduced energy of `q`. If the nullity of the iterate
is at most that of `q`, every kernel vector of the Hessian of the iterate is an iterated kernel
vector, so the reduced energy of the iterate is determined by that of `q` (Gromoll and Meyer).
No statement on local cohomology is made. -/

@[expose] public section

namespace Finsler.PolygonIterateReduction

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonIterate Finsler.LyapunovSchmidt
open Set Filter Module
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

/-- A reduction map for the coordinate energy of the polygon `q`. -/
def IsReduction (F : ReversibleMetric n) (q : ZMod N → Sphere n) (σ : Model n N → Model n N) :
    Prop :=
  ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧
    (∀ᶠ w in 𝓝 (0 : Model n N), kerProj (hessian F q) (σ w) = kerProj (hessian F q) w ∧
      cokerProj (hessian F q) (grad F q (base q + σ w)) = cokerProj (hessian F q) w) ∧
    ∀ᶠ z in 𝓝 (0 : Model n N),
      σ (kerProj (hessian F q) z + cokerProj (hessian F q) (grad F q (base q + z))) = z

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

omit [NeZero m] [NeZero N] in
include hq in
/-- The iterate of a short polygon is short. -/
theorem shortPolygon_iterate : ShortPolygon δ (iterate m N q) := fun i => by
  rw [iterate_apply, iterate_apply, map_add, map_one]
  exact hq (red m N i)

omit [NeZero m] [NeZero N] in
include hne in
/-- The iterate of a polygon without zero edges has no zero edges. -/
theorem iterate_ne (i : ZMod (m * N)) : iterate m N q (i + 1) ≠ iterate m N q i := by
  rw [iterate_apply, iterate_apply, map_add, map_one]
  exact hne (red m N i)

include hδ hq hne in
/-- The gradient of the coordinate energy of the iterate at an iterated point. -/
theorem eventually_grad_iterate :
    ∀ᶠ x in 𝓝 (base q), grad F (iterate m N q) (iterL m N x) =
      (m : ℝ) • iterL m N (grad F q x) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have h₀ := eventually_hasFDerivAt F hδ hq hne
  have h₁ := eventually_hasFDerivAt F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne)
  have ht : Tendsto (iterL (n := n) m N) (𝓝 (base q)) (𝓝 (base (iterate m N q))) := by
    rw [base_iterate]
    exact (iterL m N).continuous.tendsto _
  filter_upwards [h₀, ht.eventually h₁] with x hx₀ hx₁
  have hfix : shiftL m N (grad F (iterate m N q) (iterL m N x)) =
      grad F (iterate m N q) (iterL m N x) :=
    ReductionNaturality.gradient_fixed (inner_shiftL m N) (shiftL_iterL m N x)
      (Eventually.of_forall fun z => energy_shiftL m N F q z) hx₁
  have h := ReductionNaturality.gradient_map (κ := (m : ℝ)) (d := (m : ℝ) ^ 2) hm
    (inner_iterL m N) (Eventually.of_forall fun y => energy_iterate m N F q y) hx₀ hx₁
    (exists_of_shiftL_eq m N hfix)
  rw [h]
  congr 1
  field_simp

include hδ hq hne in
/-- The same in coordinates centred at the polygons. -/
theorem eventually_grad_iterate_add :
    ∀ᶠ z in 𝓝 (0 : Model n N), grad F (iterate m N q) (base (iterate m N q) + iterL m N z) =
      (m : ℝ) • iterL m N (grad F q (base q + z)) := by
  have ht : Tendsto (fun z : Model n N => base q + z) (𝓝 0) (𝓝 (base q)) := by
    have h : ContinuousAt (fun z : Model n N => base q + z) 0 :=
      continuousAt_const.add continuousAt_id
    have h' := h.tendsto
    rwa [add_zero] at h'
  filter_upwards [ht.eventually (eventually_grad_iterate m N F hδ hq hne)] with z hz
  rw [base_iterate, ← map_add]
  exact hz

include hδ hq hne in
/-- The Hessian of the iterate on iterated vectors. -/
theorem hessian_iterate (v : Model n N) :
    hessian F (iterate m N q) (iterL m N v) = (m : ℝ) • iterL m N (hessian F q v) :=
  ReductionNaturality.map_deriv (grad_hasFDerivAt F hδ hq hne)
    (grad_hasFDerivAt F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne))
    (eventually_grad_iterate_add m N F hδ hq hne) v

include hδ hq hne in
/-- The nullity does not decrease under iteration. -/
theorem nullity_le_iterate : nullity F q ≤ nullity F (iterate m N q) :=
  ReductionNaturality.finrank_ker_le (hessian_iterate m N F hδ hq hne) (iterL_injective m N)

include hδ hq hne in
/-- If the nullity of the iterate is at most the nullity of the polygon, every kernel vector of
the Hessian of the iterate is an iterated kernel vector. -/
theorem exists_of_nullity_le (hnull : nullity F (iterate m N q) ≤ nullity F q)
    {k : Model n (m * N)} (hk : hessian F (iterate m N q) k = 0) :
    ∃ w, hessian F q w = 0 ∧ iterL m N w = k :=
  ReductionNaturality.exists_of_finrank_le (hessian_iterate m N F hδ hq hne)
    (iterL_injective m N) hnull hk

include hδ hq hne in
/-- A stationary short polygon without zero edges has a reduction map. -/
theorem exists_isReduction (hc : PolyCritical F N q) : ∃ σ, IsReduction N F q σ := by
  obtain ⟨σ, hσ, hσ0, -, hr, hl⟩ := LyapunovSchmidt.exists_reduction
    (hessian_isSymmetric F hδ hq hne) (k := 2) (by norm_num) (grad_contDiffAt F hδ hq hne)
    (grad_hasFDerivAt F hδ hq hne) (grad_eq_zero_of_polyCritical F hδ hq hne hc)
  exact ⟨σ, hσ, hσ0, hr, hl⟩

include hδ hq hne in
/-- The gradient vanishes at the iterate of a stationary polygon. -/
theorem grad_iterate_eq_zero (hc : PolyCritical F N q) :
    grad F (iterate m N q) (base (iterate m N q)) = 0 := by
  have h := (eventually_grad_iterate m N F hδ hq hne).self_of_nhds
  rw [base_iterate, h, grad_eq_zero_of_polyCritical F hδ hq hne hc, map_zero, smul_zero]

include hδ hq hne in
/-- The iterate of a stationary short polygon without zero edges has a reduction map. -/
theorem exists_isReduction_iterate (hc : PolyCritical F N q) :
    ∃ σ, IsReduction (m * N) F (iterate m N q) σ := by
  obtain ⟨σ, hσ, hσ0, -, hr, hl⟩ := LyapunovSchmidt.exists_reduction
    (hessian_isSymmetric F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne)) (k := 2)
    (by norm_num)
    (grad_contDiffAt F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne))
    (grad_hasFDerivAt F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne))
    (grad_iterate_eq_zero m N F hδ hq hne hc)
  exact ⟨σ, hσ, hσ0, hr, hl⟩

include hδ hq hne in
/-- Reduction maps of a polygon and of its iterate are intertwined by the iteration map on the
kernel of the Hessian, and the reduced energy of the iterate there is `m²` times the reduced
energy of the polygon. -/
theorem eventually_reduction_iterate {σ₀ : Model n N → Model n N}
    {σ : Model n (m * N) → Model n (m * N)} (h₀ : IsReduction N F q σ₀)
    (h : IsReduction (m * N) F (iterate m N q) σ) :
    ∀ᶠ w in 𝓝 (0 : Model n N), hessian F q w = 0 →
      σ (iterL m N w) = iterL m N (σ₀ w) ∧
      energy F (iterate m N q) (base (iterate m N q) + σ (iterL m N w)) =
        (m : ℝ) ^ 2 * energy F q (base q + σ₀ w) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hs₀ := hessian_isSymmetric F hδ hq hne
  have hs := hessian_isSymmetric F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne)
  obtain ⟨hσ₀, hσ₀0, hr₀, -⟩ := h₀
  obtain ⟨-, -, -, hl⟩ := h
  have hf : ∀ᶠ z in 𝓝 (0 : Model n N),
      energy F (iterate m N q) (base (iterate m N q) + iterL m N z) =
        (m : ℝ) ^ 2 * energy F q (base q + z) :=
    Eventually.of_forall fun z => by
      rw [base_iterate, ← map_add, energy_iterate]
  have h1 := ReductionNaturality.eventually_reduction_map_ker hs₀ hs hm
    (hessian_iterate m N F hδ hq hne) (eventually_grad_iterate_add m N F hδ hq hne)
    hσ₀.continuousAt hσ₀0 hr₀ hl
  have h2 := ReductionNaturality.eventually_reduced_map hs₀ hs hm
    (hessian_iterate m N F hδ hq hne) (eventually_grad_iterate_add m N F hδ hq hne)
    hσ₀.continuousAt hσ₀0 hr₀ hl hf
  filter_upwards [h1, h2] with w hw1 hw2 hAw
  exact ⟨hw1 hAw, hw2 hAw⟩

end Regular

end

end Finsler.PolygonIterateReduction
