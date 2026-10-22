import Lean
import FCSolution

open Lean Elab Command

-- Fail closed: check the transitive axioms of the published targets.
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``ReversibleFinslerSphereFC.infinitely_many_prime_closed_geodesics,
    ``ReversibleFinslerSphereFC.variational_form,
    ``Finsler.UFFillRel.reversible_sphere_assertion,
    ``Finsler.UFFillRel.ordinary_sphere_assertion]
  for target in targets do
    let axioms ← collectAxioms target
    let bad := axioms.filter fun name => !allowed.contains name
    unless bad.isEmpty do
      throwError "Disallowed axiom in {target}: {bad}"
    logInfo m!"PASS {target}: {axioms}"

#print ReversibleFinslerSphereFC.infinitely_many_prime_closed_geodesics
#print ReversibleFinslerSphereFC.variational_form

