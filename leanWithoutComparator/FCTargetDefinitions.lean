module

public import Finsler.Geometry.OrdinaryGeodesic

/-! Fixed mathematical definitions. No proof of infinitude is imported here. -/

@[expose] public section

namespace ReversibleFinslerSphereFC

/-- The Riemannian subclass of reversible Finsler metrics: each squared tangent norm is
$F(x,v)^2 = g_x(v,v)$ for a symmetric positive-definite real bilinear form $g_x$.
The tangent fibers are those of the actual smooth sphere; smoothness of $F$ is already
part of `Finsler.Geometry.ReversibleMetric`. -/
def IsRiemannian {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) : Prop :=
  ∀ x : Finsler.SphereGeometry.Sphere n,
    ∃ g : Finsler.SphereGeometry.Fiber n x →ₗ[ℝ]
        Finsler.SphereGeometry.Fiber n x →ₗ[ℝ] ℝ,
      (∀ v w, g v w = g w v) ∧
      (∀ v, v ≠ 0 → 0 < g v v) ∧
      ∀ v, F.value ⟨x, v⟩ ^ 2 = g v v

/-- Images of smooth regular one-periodic solutions of the actual coordinate
Euler–Lagrange equation of F², whose least positive period is one. -/
def PrimeClosedGeodesicImages {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) :
    Set (Set (Finsler.SphereGeometry.Sphere n)) :=
  {s | ∃ γ : Finsler.Loops.SmoothLoop n,
    Finsler.Geodesics.Regular γ ∧
    Finsler.SphereCoordinateEuler.CoordinateEuler F γ ∧
    Finsler.Loops.Primitive γ ∧ Set.range γ = s}

theorem primeClosedGeodesicImages_eq {n : ℕ}
    (F : Finsler.Geometry.ReversibleMetric n) :
    PrimeClosedGeodesicImages F = Finsler.OrdinaryGeodesics.primeImages F := by
  ext s
  constructor
  · rintro ⟨γ, hr, he, hp, hi⟩
    exact ⟨⟨γ, hr, he⟩, hp, hi⟩
  · rintro ⟨γ, hp, hi⟩
    exact ⟨γ.loop, γ.regular, γ.coordinateEuler, hp, hi⟩

end ReversibleFinslerSphereFC

