module

public import FCExactSolution
public meta import Lean.Util.CollectAxioms

/-! The full FC target type and its transitive axiom closure. -/
example (n : ℕ) (hn : 3 ≤ n) (F : ReversibleFinslerSpheres.ReversibleMetric n) :
    (ReversibleFinslerSpheres.PrimeClosedGeodesicImages F).Infinite :=
  ReversibleFinslerSpheres.infinitely_many_prime_closed_geodesics n hn F

run_cmd do
  let target := ``ReversibleFinslerSpheres.infinitely_many_prime_closed_geodesics
  let axioms ← Lean.collectAxioms target
  for name in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains name do
      throwError "Disallowed axiom in {target}: {name}"
  Lean.logInfo m!"PASS exact FC target: {target}; axioms = {axioms}"
