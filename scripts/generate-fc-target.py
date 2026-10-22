#!/usr/bin/env python3
"""Extract the exact n >= 3 FC definitions/type for proof and Comparator.

FC metadata imports/attributes are omitted. Module visibility is retained. Every
mathematical definition and the complete target signature come from the FC file.
The submission itself is never modified. No n = 2 statement is used as an axiom.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = "ReversibleFinslerSpheres.infinitely_many_prime_closed_geodesics"
IMPORTS = """public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
"""
PROOF = """  let G : Finsler.Geometry.ReversibleMetric n :=
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
"""
AUDIT = """module

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
"""


def render():
    original = (ROOT / "FClikelean/ReversibleFinslerSpheres.lean").read_text()
    definitions = original[:original.index("/-- **OpenAI's sphere theorem")]
    target = original[original.index("/-- **Higher-dimensional variant"):]
    assert target.count("sorry") == 1
    target = re.sub(r"(?m)^@\[category research solved, AMS 53\]\n", "", target)
    assert target.count("theorem ") == 1
    assert "(hn : 3 ≤ n)" in target
    prefix = definitions.replace("public import FormalConjecturesUtil\n", IMPORTS)
    assert prefix != definitions
    reference = prefix + target
    solution = (prefix.replace(IMPORTS, IMPORTS + "public import FCSolution\n") +
                target.replace("  sorry\n", PROOF))
    assert "sorry" not in solution
    return original, definitions, target, reference, solution


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    original, definitions, target, reference, solution = render()
    outputs = {"lean/FCExactChallenge.lean": reference,
               "lean/FCExactSolution.lean": solution,
               "lean/FCExactAudit.lean": AUDIT,
               "leanWithoutComparator/FCExactSolution.lean": solution,
               "leanWithoutComparator/FCExactAudit.lean": AUDIT}
    for name, content in outputs.items():
        path = ROOT / name
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit("Generated FC target differs: " + name)
        else:
            path.write_text(content)
    print(json.dumps({"status": "pass", "target": TARGET,
                      "fc_source_sha256": hashlib.sha256(original.encode()).hexdigest(),
                      "exact_mathematical_definitions_sha256": hashlib.sha256(
                          definitions[definitions.index("namespace ReversibleFinslerSpheres"):].encode()).hexdigest(),
                      "omitted_only": ["FC metadata umbrella import (replaced by used Mathlib imports)",
                                       "research-solved/AMS metadata attribute", "other three theorem statements"],
                      "generated_files": list(outputs)}, indent=2))


if __name__ == "__main__":
    main()
