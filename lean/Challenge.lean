import FCTargetDefinitions

/-! Comparator reference. The two placeholders specify tasks, not proofs.
This module must never be imported by FCSolution or the proof library. -/
namespace ReversibleFinslerSphereFC

/-- Every smooth strongly convex reversible Finsler metric on Sⁿ, n ≥ 3,
has infinitely many geometrically distinct prime closed geodesics. -/
theorem infinitely_many_prime_closed_geodesics (n : ℕ) (hn : 3 ≤ n)
    (F : Finsler.Geometry.ReversibleMetric n) :
    (PrimeClosedGeodesicImages F).Infinite := by
  sorry

/-- Equivalent formulation using stationarity of the integral energy. -/
theorem variational_form (n : ℕ) (hn : 3 ≤ n)
    (F : Finsler.Geometry.ReversibleMetric n) :
    (Finsler.Geodesics.primeImages F).Infinite := by
  sorry

end ReversibleFinslerSphereFC

