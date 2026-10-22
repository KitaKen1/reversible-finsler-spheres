module

public import FCTargetDefinitions
public import Finsler.Residual.FillRel

public section

namespace ReversibleFinslerSphereFC

/-- Every smooth strongly convex reversible Finsler metric on Sⁿ, n ≥ 3,
has infinitely many geometrically distinct prime closed geodesics. -/
theorem infinitely_many_prime_closed_geodesics (n : ℕ) (hn : 3 ≤ n)
    (F : Finsler.Geometry.ReversibleMetric n) :
    (PrimeClosedGeodesicImages F).Infinite := by
  rw [primeClosedGeodesicImages_eq]
  exact Finsler.UFFillRel.ordinary_sphere_assertion n hn F

/-- Equivalent formulation using stationarity of the integral energy. -/
theorem variational_form (n : ℕ) (hn : 3 ≤ n)
    (F : Finsler.Geometry.ReversibleMetric n) :
    (Finsler.Geodesics.primeImages F).Infinite := by
  exact Finsler.UFFillRel.reversible_sphere_assertion n hn F

end ReversibleFinslerSphereFC

