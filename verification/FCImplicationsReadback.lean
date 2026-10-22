import Lean
import FCImplications

open Lean Elab Command ReversibleFinslerSphereFC

-- Exact quantifiers, including the remaining hypothesis in the conditional result.
example : FinslerTwoSphereAssertion =
    (∀ F : Finsler.Geometry.ReversibleMetric 2,
      (PrimeClosedGeodesicImages F).Infinite) := rfl

example : FinslerAllDimensionsAssertion =
    (∀ (n : ℕ), 2 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
      (PrimeClosedGeodesicImages F).Infinite) := rfl

example : RiemannianAllDimensionsAssertion =
    (∀ (n : ℕ), 2 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
      IsRiemannian F → (PrimeClosedGeodesicImages F).Infinite) := rfl

example : FinslerAllDimensionsAssertion ↔ FinslerTwoSphereAssertion :=
  finsler_all_dimensions_iff_two_sphere

example : FinslerAllDimensionsAssertion → RiemannianAllDimensionsAssertion :=
  riemannian_all_dimensions_of_finsler

example : ∀ (n : ℕ), 3 ≤ n → ∀ F : Finsler.Geometry.ReversibleMetric n,
    IsRiemannian F → (PrimeClosedGeodesicImages F).Infinite :=
  riemannian_infinitely_many_prime_closed_geodesics_of_three_le

-- Reject a transitive placeholder or custom axiom, including accidental imports
-- from the FC draft. A named hypothesis is still visible in each theorem's type.
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``riemannian_of_finsler_at_dimension,
    ``riemannian_infinitely_many_prime_closed_geodesics_of_three_le,
    ``finsler_all_dimensions_of_two_sphere,
    ``finsler_all_dimensions_iff_two_sphere,
    ``riemannian_all_dimensions_of_finsler,
    ``riemannian_all_dimensions_of_two_sphere]
  for target in targets do
    let axioms ← collectAxioms target
    let bad := axioms.filter fun name => !allowed.contains name
    unless bad.isEmpty do
      throwError "Disallowed axiom in {target}: {bad}"
    logInfo m!"PASS {target}: {axioms}"

#print finsler_all_dimensions_of_two_sphere
#print riemannian_all_dimensions_of_two_sphere
