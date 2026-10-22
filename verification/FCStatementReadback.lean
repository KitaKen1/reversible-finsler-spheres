import ReversibleFinslerSpheres

/-! Readback of the four independent FC statement types and metadata. The four statements deliberately contain placeholders: applying them here
checks their types, not their proofs. -/

open ReversibleFinslerSpheres
open scoped RealInnerProductSpace

-- FC research status is metadata, independent of the four proof placeholders.
run_cmd do
  let env ← Lean.getEnv
  let categories := (ProblemAttributes.categoryExt.getState env).toList
  let subjects := (ProblemAttributes.subjectExt.getState env).toList
  let targets : List Lean.Name := [
    ``riemannian_infinitely_many_prime_closed_geodesics,
    ``finsler_infinitely_many_prime_closed_geodesics,
    ``finsler_two_sphere_infinitely_many_prime_closed_geodesics,
    ``infinitely_many_prime_closed_geodesics]
  for target in targets do
    unless categories.any (fun tag => tag.declName == target &&
        tag.category == .research .solved) do
      throwError "Missing FC research-solved category: {target}"
    unless subjects.any (fun tag => tag.declName == target && tag.subjects.contains AMS.«53») do
      throwError "Missing AMS 53 tag: {target}"
  Lean.logInfo "PASS: four genuine FC research-solved / AMS 53 attributes"

example : ∀ (n : ℕ), 2 ≤ n → ∀ F : ReversibleMetric n,
    IsRiemannian F → (PrimeClosedGeodesicImages F).Infinite :=
  riemannian_infinitely_many_prime_closed_geodesics

example : ∀ (n : ℕ), 2 ≤ n → ∀ F : ReversibleMetric n,
    (PrimeClosedGeodesicImages F).Infinite :=
  finsler_infinitely_many_prime_closed_geodesics

example : ∀ F : ReversibleMetric 2, (PrimeClosedGeodesicImages F).Infinite :=
  finsler_two_sphere_infinitely_many_prime_closed_geodesics

example : ∀ (n : ℕ), 3 ≤ n → ∀ F : ReversibleMetric n,
    (PrimeClosedGeodesicImages F).Infinite :=
  infinitely_many_prime_closed_geodesics

