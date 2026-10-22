import Lean
import FCSolution
import Finsler.Geometry.RoundMetric

/-! Executable statement correspondence, not a proof that English has a unique interpretation. -/

open Lean Elab Command
open scoped Manifold ContDiff

example : Finsler.Geodesics.ReversibleSphereAssertion =
    (∀ n : ℕ, 3 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
      (Finsler.Geodesics.primeImages F).Infinite) := rfl

example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (γ : Finsler.Loops.SmoothLoop n) : Finsler.Geodesics.Stationary F γ =
    (∀ V : Finsler.Geodesics.SmoothVariation n,
      Finsler.Geodesics.loopAt V 0 = γ →
        HasDerivAt (fun s => Finsler.LoopEnergy.energy F
          (Finsler.Geodesics.loopAt V s)) 0 0) := rfl

example {n : ℕ} (γ : Finsler.Loops.SmoothLoop n) :
    Finsler.Geodesics.Regular γ =
      (∀ t, TauCeti.Manifold.curveVelocity (𝓡 n) γ t ≠ 0) := rfl

example (n : ℕ) : Finsler.SphereGeometry.Sphere n =
    ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := rfl

example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) :
    Finsler.Geodesics.primeImages F =
      {s | ∃ γ : Finsler.Geodesics.ClosedGeodesic F,
        Finsler.Loops.Primitive γ.loop ∧ Set.range γ.loop = s} := rfl

example {n : ℕ} (γ : Finsler.Loops.SmoothLoop n) : Finsler.Loops.Primitive γ =
    (∀ T : ℝ, 0 < T → Function.Periodic γ T → 1 ≤ T) := rfl

example {n : ℕ} : ∀ (F : Finsler.Geometry.ReversibleMetric n)
    (x : Finsler.SphereGeometry.Sphere n) (v w : Finsler.SphereGeometry.Fiber n x),
    v ≠ 0 → w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u : Finsler.SphereGeometry.Fiber n x =>
        F.value ⟨x, u⟩ ^ 2 / 2)) v w w := Finsler.Geometry.ReversibleMetric.strongConvex

example (n : ℕ) : Nonempty (Finsler.Geometry.ReversibleMetric n) :=
  Finsler.Geometry.reversibleMetric_nonempty n

example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (γ : Finsler.Loops.SmoothLoop n) :
    Finsler.SphereCoordinateEuler.CoordinateEuler F γ =
      (∀ (p : Finsler.SphereGeometry.Sphere n) (t : ℝ),
        γ t ∈ (extChartAt (𝓡 n) p).source →
          Finsler.SphereCoordinateEuler.coordinateResidual F p γ t = 0) := rfl

example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (p : Finsler.SphereGeometry.Sphere n) (γ : Finsler.Loops.SmoothLoop n) (t : ℝ) :
    Finsler.SphereCoordinateEuler.coordinateResidual F p γ t =
      Finsler.EulerCovariance.positionTerm
        (Finsler.SphereCoordinateEuler.coordinateLagrangian F p)
        (Finsler.EulerCovariance.curveJet
          (Finsler.SphereCoordinateEuler.coordinateCurve p γ) t) -
      deriv (Finsler.EulerCovariance.momentum
        (Finsler.SphereCoordinateEuler.coordinateLagrangian F p)
        (Finsler.SphereCoordinateEuler.coordinateCurve p γ)) t := rfl

example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (p : Finsler.SphereGeometry.Sphere n) {y : Finsler.SphereCoordinateEuler.Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) (w : Finsler.SphereCoordinateEuler.Coordinates n) :
    Finsler.SphereCoordinateEuler.coordinateLagrangian F p (y, w) =
      F.value ⟨Finsler.SphereCoordinateEuler.inverseSphere p y,
        mfderiv 𝓘(ℝ, Finsler.SphereCoordinateEuler.Coordinates n) (𝓡 n)
          (Finsler.SphereCoordinateEuler.inverseSphere p) y w⟩ ^ 2 :=
  Finsler.SphereCoordinateEuler.coordinateLagrangian_eq F p hy w

example : Finsler.OrdinaryGeodesics.ReversibleSphereAssertion =
    (∀ n : ℕ, 3 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
      (Finsler.OrdinaryGeodesics.primeImages F).Infinite) := rfl

example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) :
    Finsler.OrdinaryGeodesics.primeImages F =
      {s | ∃ γ : Finsler.OrdinaryGeodesics.ClosedGeodesic F,
        Finsler.Loops.Primitive γ.loop ∧ Set.range γ.loop = s} := rfl

example : Finsler.Geodesics.ReversibleSphereAssertion ↔
    Finsler.OrdinaryGeodesics.ReversibleSphereAssertion :=
  Finsler.OrdinaryGeodesics.assertion_iff


-- Expanded publication target equals the ordinary geometric-image set.
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) :
    ReversibleFinslerSphereFC.PrimeClosedGeodesicImages F =
      Finsler.OrdinaryGeodesics.primeImages F :=
  ReversibleFinslerSphereFC.primeClosedGeodesicImages_eq F

-- Check the complete quantifier prefix: there is no extra hypothesis.
example : ∀ n : ℕ, 3 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
    (ReversibleFinslerSphereFC.PrimeClosedGeodesicImages F).Infinite :=
  ReversibleFinslerSphereFC.infinitely_many_prime_closed_geodesics

-- All metric conditions are properties of the actual tangent-bundle function.
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) : Continuous F.value :=
  F.continuous
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) :
    ContMDiffOn (𝓡 n).tangent 𝓘(ℝ, ℝ) ∞ F.value
      (Finsler.Geometry.slitBundle n) := F.smooth
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (x : Finsler.SphereGeometry.Sphere n) : F.value ⟨x, 0⟩ = 0 := F.zero x
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (x : Finsler.SphereGeometry.Sphere n) (v : Finsler.SphereGeometry.Fiber n x)
    (hv : v ≠ 0) : 0 < F.value ⟨x, v⟩ := F.positive x v hv
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (x : Finsler.SphereGeometry.Sphere n) (v : Finsler.SphereGeometry.Fiber n x)
    (r : ℝ) (hr : 0 ≤ r) : F.value ⟨x, r • v⟩ = r * F.value ⟨x, v⟩ :=
  F.homogeneous x v r hr
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (x : Finsler.SphereGeometry.Sphere n) (v : Finsler.SphereGeometry.Fiber n x) :
    F.value ⟨x, -v⟩ = F.value ⟨x, v⟩ := F.reversible x v

-- Phase shifts, orientation reversal and positive iteration keep the same image.
example {n : ℕ} (γ : Finsler.Loops.SmoothLoop n) (a : ℝ) :
    Finsler.Loops.image (Finsler.Loops.shift γ a) = Finsler.Loops.image γ :=
  Finsler.Loops.image_shift γ a
example {n : ℕ} (γ : Finsler.Loops.SmoothLoop n) :
    Finsler.Loops.image (Finsler.Loops.reverse γ) = Finsler.Loops.image γ :=
  Finsler.Loops.image_reverse γ
example {n : ℕ} (γ : Finsler.Loops.SmoothLoop n) {k : ℕ} (hk : k ≠ 0) :
    Finsler.Loops.image (Finsler.Loops.iterate γ k) = Finsler.Loops.image γ :=
  Finsler.Loops.image_iterate γ hk

-- Geodesic regularity implies strictly positive actual integral energy.
example {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (γ : Finsler.Loops.SmoothLoop n) (h : Finsler.Geodesics.Regular γ) :
    0 < Finsler.LoopEnergy.energy F γ := Finsler.Geodesics.regular_energy_pos F γ h

#eval IO.println "PASS: publication specification readback"
