module

public import Finsler.Geometry.PolygonMonodromy

/-! The types of the iterates of a short polygon (Gromoll and Meyer). For a short polygon
without zero edges with the twist condition there is L ≥ 1 with the following property. If
gcd(d k, L) = gcd(d, L), every kernel vector of the Hessian of the (d k)-fold iterate is the
k-fold iterate of a kernel vector of the Hessian of the d-fold iterate, reduction maps of the
two iterates are intertwined by the iteration map on the kernel, and the reduced energy of the
(d k)-fold iterate is k² times the reduced energy of the d-fold iterate. Hence the reduced
energies of all iterates are determined, up to these scalings, by those of the d-fold iterates
with d dividing L: only finitely many types occur. The radius below which every polygon
without zero edges has such a period is uniform. No statement on indices or local cohomology
is made. -/

@[expose] public section

namespace Finsler.PolygonTypes

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonNullity Finsler.PolygonIterate Finsler.PolygonIterateReduction
open Set Filter Module
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n N : ℕ} [NeZero N]

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- A short polygon without zero edges at which the gradient of the coordinate energy vanishes
has a reduction map. -/
theorem exists_isReduction_of_grad (hg : grad F q (base q) = 0) : ∃ σ, IsReduction N F q σ := by
  obtain ⟨σ, hσ, hσ0, -, hr, hl⟩ := LyapunovSchmidt.exists_reduction
    (hessian_isSymmetric F hδ hq hne) (k := 2) (by norm_num) (grad_contDiffAt F hδ hq hne)
    (grad_hasFDerivAt F hδ hq hne) hg
  exact ⟨σ, hσ, hσ0, hr, hl⟩

include hδ hq hne in
/-- The gradient vanishes at the iterates of a polygon at which it vanishes. -/
theorem grad_iterate_eq_zero_of_grad (d : ℕ) [NeZero d] (hg : grad F q (base q) = 0) :
    grad F (iterate d N q) (base (iterate d N q)) = 0 := by
  have h := (eventually_grad_iterate d N F hδ hq hne).self_of_nhds
  rw [base_iterate, h, hg, map_zero, smul_zero]

include hδ hq hne in
/-- **The types of the iterates.** Under the twist condition there is L ≥ 1 such that, whenever
gcd(d k, L) = gcd(d, L), the kernel of the Hessian of the (d k)-fold iterate consists of the
iterated kernel vectors of the d-fold iterate, and the reduced energy of the (d k)-fold iterate
is k² times the reduced energy of the d-fold iterate. -/
theorem exists_types_of_twist (htw : Twist F q) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ (d k : ℕ) [NeZero d] [NeZero k], Nat.gcd (d * k) L = Nat.gcd d L →
      (∀ κ : Model n (k * (d * N)), hessian F (iterate k (d * N) (iterate d N q)) κ = 0 →
        ∃ w, hessian F (iterate d N q) w = 0 ∧ iterL k (d * N) w = κ) ∧
      ∀ (σ₀ : Model n (d * N) → Model n (d * N))
        (σ : Model n (k * (d * N)) → Model n (k * (d * N))),
        IsReduction (d * N) F (iterate d N q) σ₀ →
        IsReduction (k * (d * N)) F (iterate k (d * N) (iterate d N q)) σ →
        ∀ᶠ w in 𝓝 (0 : Model n (d * N)), hessian F (iterate d N q) w = 0 →
          σ (iterL k (d * N) w) = iterL k (d * N) (σ₀ w) ∧
          energy F (iterate k (d * N) (iterate d N q))
              (base (iterate k (d * N) (iterate d N q)) + σ (iterL k (d * N) w)) =
            (k : ℝ) ^ 2 * energy F (iterate d N q) (base (iterate d N q) + σ₀ w) := by
  obtain ⟨L, hL, -, hper⟩ := PolygonMonodromy.exists_period F hδ hq hne htw
  refine ⟨L, hL, fun d k _ _ hg => ⟨fun κ hκ => ?_, fun σ₀ σ h₀ h => ?_⟩⟩
  · exact exists_of_nullity_le k (d * N) F hδ (shortPolygon_iterate d N hq)
      (iterate_ne d N hne) (hper d k hg).le hκ
  · exact eventually_reduction_iterate k (d * N) F hδ (shortPolygon_iterate d N hq)
      (iterate_ne d N hne) h₀ h

end Regular

/-- **Finitely many types, uniformly.** There is a positive radius below which every polygon
without zero edges, with any number of vertices, has a period L ≥ 1 as in
`exists_types_of_twist`. -/
theorem exists_types (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) →
      ∃ L : ℕ, 1 ≤ L ∧ ∀ (d k : ℕ) [NeZero d] [NeZero k], Nat.gcd (d * k) L = Nat.gcd d L →
        (∀ κ : Model n (k * (d * N)), hessian F (iterate k (d * N) (iterate d N q)) κ = 0 →
          ∃ w, hessian F (iterate d N q) w = 0 ∧ iterL k (d * N) w = κ) ∧
        ∀ (σ₀ : Model n (d * N) → Model n (d * N))
          (σ : Model n (k * (d * N)) → Model n (k * (d * N))),
          IsReduction (d * N) F (iterate d N q) σ₀ →
          IsReduction (k * (d * N)) F (iterate k (d * N) (iterate d N q)) σ →
          ∀ᶠ w in 𝓝 (0 : Model n (d * N)), hessian F (iterate d N q) w = 0 →
            σ (iterL k (d * N) w) = iterL k (d * N) (σ₀ w) ∧
            energy F (iterate k (d * N) (iterate d N q))
                (base (iterate k (d * N) (iterate d N q)) + σ (iterL k (d * N) w)) =
              (k : ℝ) ^ 2 * energy F (iterate d N q) (base (iterate d N q) + σ₀ w) := by
  obtain ⟨δ₁, hδ₁, htw⟩ := PolygonTwist.exists_twist F
  obtain ⟨δ₂, hδ₂, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun N _ q hq hne => ?_⟩
  have hq₁ : ShortPolygon δ₁ q := fun i => (hq i).trans_le (min_le_left _ _)
  have hq₂ : ShortPolygon δ₂ q := fun i => (hq i).trans_le (min_le_right _ _)
  exact exists_types_of_twist F hs hq₂ hne (htw N q hq₁ hne)

end

end Finsler.PolygonTypes
