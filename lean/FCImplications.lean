import FCSolution

/-!
# Relationships between the four FC statements

These proofs import the proved higher-dimensional result, never the FC statement
file. The two-sphere assertion remains an explicit hypothesis where needed.
In particular, the implications below are not proofs of the unprovided
two-dimensional theorem.
-/

namespace ReversibleFinslerSphereFC

/-- The exact missing two-dimensional Finsler assertion. -/
def FinslerTwoSphereAssertion : Prop :=
  ∀ F : Finsler.Geometry.ReversibleMetric 2, (PrimeClosedGeodesicImages F).Infinite

/-- The all-dimensional Finsler assertion, with the same quantifiers as FC statement 2. -/
def FinslerAllDimensionsAssertion : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
    (PrimeClosedGeodesicImages F).Infinite

/-- The Riemannian sphere assertion, with the same quantifiers as FC statement 1. -/
def RiemannianAllDimensionsAssertion : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
    IsRiemannian F → (PrimeClosedGeodesicImages F).Infinite

/-- Any Finsler infinitude result at a fixed dimension also applies to the
Riemannian subclass at that dimension. -/
theorem riemannian_of_finsler_at_dimension (n : ℕ)
    (h : ∀ F : Finsler.Geometry.ReversibleMetric n,
      (PrimeClosedGeodesicImages F).Infinite)
    (F : Finsler.Geometry.ReversibleMetric n) (_hF : IsRiemannian F) :
    (PrimeClosedGeodesicImages F).Infinite :=
  h F

/-- The Riemannian specialization of the proved n ≥ 3 theorem. -/
theorem riemannian_infinitely_many_prime_closed_geodesics_of_three_le
    (n : ℕ) (hn : 3 ≤ n) (F : Finsler.Geometry.ReversibleMetric n)
    (hF : IsRiemannian F) : (PrimeClosedGeodesicImages F).Infinite :=
  riemannian_of_finsler_at_dimension n
    (infinitely_many_prime_closed_geodesics n hn) F hF

/-- Combining an actual proof of the two-sphere case with the existing n ≥ 3
proof would establish FC statement 2. The two-sphere proof is an explicit input. -/
theorem finsler_all_dimensions_of_two_sphere (h2 : FinslerTwoSphereAssertion) :
    FinslerAllDimensionsAssertion := by
  intro n hn F
  by_cases h : n = 2
  · subst n
    exact h2 F
  · exact infinitely_many_prime_closed_geodesics n (by omega) F

/-- With the higher-dimensional theorem already proved, the complete Finsler
assertion is equivalent to its missing two-dimensional case. -/
theorem finsler_all_dimensions_iff_two_sphere :
    FinslerAllDimensionsAssertion ↔ FinslerTwoSphereAssertion := by
  constructor
  · intro h F
    exact h 2 (by omega) F
  · exact finsler_all_dimensions_of_two_sphere

/-- FC statement 2 implies FC statement 1 without any change to the image set. -/
theorem riemannian_all_dimensions_of_finsler
    (h : FinslerAllDimensionsAssertion) : RiemannianAllDimensionsAssertion := by
  intro n hn F hF
  exact riemannian_of_finsler_at_dimension n (h n hn) F hF

/-- The two-sphere Finsler theorem would complete the Riemannian assertion as well. -/
theorem riemannian_all_dimensions_of_two_sphere
    (h2 : FinslerTwoSphereAssertion) : RiemannianAllDimensionsAssertion :=
  riemannian_all_dimensions_of_finsler (finsler_all_dimensions_of_two_sphere h2)

end ReversibleFinslerSphereFC
