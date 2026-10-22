/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import FCSolution

/-!
# Infinitely many closed geodesic images on Riemannian spheres

Does every smooth Riemannian metric on the standard sphere $S^n$, in dimension $n \ge 2$,
have infinitely many geometrically distinct prime closed geodesics? OpenAI [OAI26]
presents a proof of this assertion for arbitrary smooth metrics, including degenerate
ones. The first theorem below records this sphere assertion, with no curvature,
bumpiness or nondegeneracy assumption.

*References:*
- [OAI26] OpenAI, *Infinitely many closed geodesic images on every Riemannian sphere*
  (September 24, 2026), OpenAI Math Release preprint, catalogue entry 345.
  [PDF](https://github.com/openai/math/blob/main/preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026/paper.pdf)
- [DPMMS22] G. De Philippis, M. Marini, M. Mazzucchelli and S. Suhr,
  *Closed geodesics on reversible Finsler 2-spheres*, Journal of Fixed Point Theory and
  Applications 24 (2022), Paper No. 19. [arXiv](https://arxiv.org/abs/2002.00415)
- [Ki26] K. Kitamura, *Infinitely many closed geodesics on reversible Finsler spheres*,
  Lean proof for $n \ge 3$ (2026), `lean/FCSolution.lean`.
-/

@[expose] public section

namespace ReversibleFinslerSpheres

open scoped Manifold ContDiff Interval
noncomputable section

/-- The standard smooth unit sphere in Euclidean `(n + 1)`-space. -/
abbrev Sphere (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- Its actual tangent space, with Mathlib's sphere charts. -/
abbrev Fiber (n : ℕ) (x : Sphere n) := TangentSpace (𝓡 n) x

/-- A smooth reversible Finsler metric. Strong convexity is positivity of
 the fiber Hessian of `F² / 2` off the zero section. -/
structure ReversibleMetric (n : ℕ) where
  value : TangentBundle (𝓡 n) (Sphere n) → ℝ
  continuous : Continuous value
  smooth : ContMDiffOn (𝓡 n).tangent 𝓘(ℝ, ℝ) ∞ value {p | p.2 ≠ 0}
  zero : ∀ x : Sphere n, value ⟨x, 0⟩ = 0
  positive : ∀ (x : Sphere n) (v : Fiber n x), v ≠ 0 → 0 < value ⟨x, v⟩
  homogeneous : ∀ (x : Sphere n) (v : Fiber n x) (r : ℝ),
    0 ≤ r → value ⟨x, r • v⟩ = r * value ⟨x, v⟩
  reversible : ∀ (x : Sphere n) (v : Fiber n x), value ⟨x, -v⟩ = value ⟨x, v⟩
  strongConvex : ∀ (x : Sphere n) (v w : Fiber n x), v ≠ 0 → w ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ (fun u : Fiber n x => value ⟨x, u⟩ ^ 2 / 2)) v w w

/-- The Riemannian subclass: the squared tangent norm is a positive quadratic form. -/
def IsRiemannian {n : ℕ} (F : ReversibleMetric n) : Prop :=
  ∀ x : Sphere n, ∃ g : Fiber n x →ₗ[ℝ] Fiber n x →ₗ[ℝ] ℝ,
    (∀ v w, g v w = g w v) ∧ (∀ v, v ≠ 0 → 0 < g v v) ∧
      ∀ v, F.value ⟨x, v⟩ ^ 2 = g v v

/-- The actual energy over one period, using the manifold derivative of the curve. -/
def energy {n : ℕ} (F : ReversibleMetric n) (γ : ℝ → Sphere n) : ℝ :=
  ∫ t in 0..1, F.value ⟨γ t, mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ Set.univ t (1 : ℝ)⟩ ^ 2

/-- Images of smooth regular prime closed geodesics. The period is normalized to one;
stationarity means zero first variation under every jointly smooth periodic family.
Counting images identifies shifts, reversals and iterates. -/
def PrimeClosedGeodesicImages {n : ℕ} (F : ReversibleMetric n) : Set (Set (Sphere n)) :=
  {s | ∃ γ : ℝ → Sphere n,
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ ∧ Function.Periodic γ 1 ∧
    (∀ t, mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ Set.univ t (1 : ℝ) ≠ 0) ∧
    (∀ T : ℝ, 0 < T → Function.Periodic γ T → 1 ≤ T) ∧
    (∀ V : ℝ × ℝ → Sphere n, ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ V →
      (∀ u, Function.Periodic (fun t => V (u, t)) 1) →
      (∀ t, V (0, t) = γ t) → HasDerivAt (fun u => energy F (fun t => V (u, t))) 0 0) ∧
    Set.range γ = s}

/-- **Higher-dimensional variant [Ki26].** Every smooth, strongly convex,
reversible Finsler metric on $S^n$, $n \ge 3$, has infinitely many geometrically
distinct prime closed geodesics. The separate proof is in `lean/FCSolution.lean`. -/
theorem infinitely_many_prime_closed_geodesics (n : ℕ) (hn : 3 ≤ n)
    (F : ReversibleMetric n) : (PrimeClosedGeodesicImages F).Infinite := by
  let G : Finsler.Geometry.ReversibleMetric n :=
    ⟨F.value, F.continuous, F.smooth, F.zero, F.positive,
      F.homogeneous, F.reversible, F.strongConvex⟩
  have energy_eq (γ : Finsler.Loops.SmoothLoop n) :
      Finsler.LoopEnergy.energy G γ = energy F γ := by
    simp only [Finsler.LoopEnergy.energy, Finsler.LoopEnergy.density,
      Finsler.LoopEnergy.velocityLift, TauCeti.Manifold.curveVelocityLift_apply,
      TauCeti.Manifold.curveVelocity_apply, energy, mfderivWithin_univ, G]
  have image_eq : PrimeClosedGeodesicImages F =
      ReversibleFinslerSphereFC.PrimeClosedGeodesicImages G := by
    ext s
    constructor
    · rintro ⟨γ, hs, hperiod, hr, hp, hstat, hi⟩
      let δ : Finsler.Loops.SmoothLoop n := ⟨γ, hs, hperiod⟩
      have hregular : Finsler.Geodesics.Regular δ := by
        simpa only [Finsler.Geodesics.Regular, TauCeti.Manifold.curveVelocity_apply,
          mfderivWithin_univ] using hr
      refine ⟨δ, hregular, ?_, hp, hi⟩
      apply (Finsler.SphereCoordinateEuler.stationary_iff_coordinateEuler G hregular).mp
      intro V hV
      have hbase : ∀ t, V.family (0, t) = γ t := by
        intro t
        exact congrArg (fun η : Finsler.Loops.SmoothLoop n => η t) hV
      simpa only [energy_eq, Finsler.Geodesics.loopAt] using
        hstat V.family V.smooth V.periodic hbase
    · rintro ⟨γ, hr, he, hp, hi⟩
      have hregular : ∀ t, mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ.curve Set.univ t (1 : ℝ) ≠ 0 := by
        simpa only [Finsler.Geodesics.Regular, TauCeti.Manifold.curveVelocity_apply,
          mfderivWithin_univ] using hr
      refine ⟨γ.curve, γ.smooth, γ.periodic, hregular, hp, ?_, hi⟩
      have hstat := (Finsler.SphereCoordinateEuler.stationary_iff_coordinateEuler G hr).mpr he
      intro V hs hperiod hbase
      let W : Finsler.Geodesics.SmoothVariation n := ⟨V, hs, hperiod⟩
      simpa only [energy_eq, Finsler.Geodesics.loopAt, W] using
        hstat W (Finsler.Loops.loop_ext hbase)
  rw [image_eq]
  exact ReversibleFinslerSphereFC.infinitely_many_prime_closed_geodesics n hn G

end

end ReversibleFinslerSpheres
