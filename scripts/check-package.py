#!/usr/bin/env python3
"""Check the sealed publication inventory, proof parity and permitted placeholders."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def code_only(s):
    # Lean has nested block comments. Mask comments and quoted strings before scanning.
    out, i, depth = [], 0, 0
    while i < len(s):
        if depth:
            if s.startswith("/-", i): depth += 1; i += 2
            elif s.startswith("-/", i): depth -= 1; i += 2
            else: out.append("\n" if s[i] == "\n" else " "); i += 1
        elif s.startswith("/-", i): depth = 1; i += 2; out.append(" ")
        elif s.startswith("--", i):
            end = s.find("\n", i)
            i = len(s) if end < 0 else end
            out.append(" ")
        elif s[i] == '"':
            i += 1
            while i < len(s):
                if s[i] == "\\": i += 2
                elif s[i] == '"': i += 1; break
                else: i += 1
            out.append(" ")
        else: out.append(s[i]); i += 1
    if depth:
        raise AssertionError("Unclosed Lean block comment")
    return "".join(out)

def main():
    proof = json.loads((ROOT / "verification/proof-source-manifest.json").read_text())["files_sha256"]
    for variant in ["lean", "leanWithoutComparator"]:
        actual = {str(p.relative_to(ROOT / variant)) for p in (ROOT / variant / "Finsler").rglob("*.lean")}
        actual.add("Finsler.lean")
        assert actual == set(proof), "Proof inventory mismatch: " + variant
        for name, expected in proof.items():
            assert digest(ROOT / variant / name) == expected, "Proof changed: " + variant + "/" + name
    for name in ["FCTargetDefinitions.lean", "FCSolution.lean", "FCExactSolution.lean", "FCExactAudit.lean", "FCImplications.lean",
                 "HingstonArithmetic.lean", "HingstonBlocks.lean", "HingstonConnectors.lean", "HingstonPause.lean", "HingstonFilling.lean", "SurfaceLocalHomology.lean", "SurfacePolygonHomology.lean", "SurfaceMorseData.lean", "SurfaceSpectralDisk.lean", "SurfacePhaseGeometry.lean", "SurfaceIteration.lean", "SurfaceIterationHomology.lean", "SurfaceIterationEquivalence.lean", "SurfaceChainIndex.lean", "SurfaceZeroMeanIndex.lean", "SurfaceOrbitModel.lean", "SurfaceMinimax.lean", "FCTwoSphere.lean", "FCAudit.lean",
                 "SpecificationReadback.lean", "lean-toolchain", "lake-manifest.json"]:
        assert (ROOT / "lean" / name).read_bytes() == (ROOT / "leanWithoutComparator" / name).read_bytes(), name
    assert not (ROOT / "leanWithoutComparator/Challenge.lean").exists()
    assert not (ROOT / "leanWithoutComparator/FCExactChallenge.lean").exists()
    assert not (ROOT / "leanWithoutComparator/comparator.json").exists()
    allowed = {"lean/Challenge.lean": 2, "lean/FCExactChallenge.lean": 1,
               "FClikelean/ReversibleFinslerSpheres.lean": 4}
    count = 0
    for base in ["lean", "leanWithoutComparator", "FClikelean", "verification"]:
        for path in (ROOT / base).rglob("*.lean"):
            if ".lake" in path.parts: continue
            relative = str(path.relative_to(ROOT))
            code = code_only(path.read_text())
            holes = len(re.findall(r"\b(?:sorry|admit|sorryAx)\b", code))
            assert holes == allowed.get(relative, 0), "Unexpected proof placeholder: " + relative
            assert not re.search(r"(?m)^\s*(?:public\s+)?axiom\s", code), "Project axiom: " + relative
            if relative not in allowed:
                assert not re.search(r"(?m)^\s*(?:public\s+)?import\s+(?:Challenge|FCExactChallenge)\b", code), relative
            count += 1
    # Comparator and solution retain identical signatures. FC has independent
    # definitions; their mathematical correspondence is proved in Lean separately.
    pattern = r"theorem infinitely_many_prime_closed_geodesics\b(.*?) := by"
    statements = []
    for name in ["lean/Challenge.lean", "lean/FCSolution.lean"]:
        match = re.search(pattern, (ROOT / name).read_text(), re.S)
        assert match, name
        statements.append(" ".join(match.group(1).split()))
    assert len(set(statements)) == 1, "Challenge/solution statement mismatch"
    subprocess.run(["python3", str(ROOT / "scripts/generate-fc-target.py"), "--check"], check=True)
    fc_root = ROOT / "FClikelean"
    fc_files = sorted(str(p.relative_to(fc_root)) for p in fc_root.rglob("*.lean"))
    assert fc_files == ["ReversibleFinslerSpheres.lean"], "FC must have one submission file"
    fc_code = code_only((fc_root / fc_files[0]).read_text())
    assert re.search(r"(?m)^module$", fc_code)
    assert "@[expose] public section" in fc_code
    fc_imports = re.findall(r"(?m)^public import\s+(\S+)\s*$", fc_code)
    assert fc_imports == ["FormalConjecturesUtil"], "Use FC's standard environment"
    assert len(re.findall(r"(?m)^\s*(?:public\s+)?import\s+", fc_code)) == 1
    assert re.findall(r"(?m)^namespace\s+(\w+)", fc_code) == ["ReversibleFinslerSpheres"]
    assert re.findall(r"(?m)^def\s+(\w+)", fc_code) == [
        "IsRiemannian", "energy", "PrimeClosedGeodesicImages"]
    assert re.findall(r"(?m)^structure\s+(\w+)", fc_code) == ["ReversibleMetric"]
    assert re.findall(r"(?m)^abbrev\s+(\w+)", fc_code) == ["Sphere", "Fiber"]
    fc_theorems = re.findall(r"(?m)^theorem\s+(\w+)", fc_code)
    assert fc_theorems == ["riemannian_infinitely_many_prime_closed_geodesics",
                           "finsler_infinitely_many_prime_closed_geodesics",
                           "finsler_two_sphere_infinitely_many_prime_closed_geodesics",
                           "infinitely_many_prime_closed_geodesics"], "FC theorem inventory/order changed"

    manifest = json.loads((ROOT / "PUBLICATION-MANIFEST.json").read_text())["files_sha256"]
    excluded = {".local-check", "runtime-results", ".git", ".lake", "__pycache__"}
    actual_files = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*")
                    if p.is_file() and not any(part in excluded for part in p.relative_to(ROOT).parts)
                    and p.name not in {"PUBLICATION-MANIFEST.json", ".DS_Store"}}
    assert actual_files == set(manifest), "Publication file inventory changed"
    for name, expected in manifest.items():
        assert digest(ROOT / name) == expected, "Publication hash mismatch: " + name
    print(json.dumps({"status": "pass", "proof_files_per_variant": len(proof),
                      "lean_files_scanned": count, "permitted_statement_placeholders": allowed,
                      "challenge_solution_signature": "identical",
                      "fc_submission": "one file; one namespace; standard upstream FormalConjecturesUtil import",
                      "fc_definition_correspondence": "verification/FCDefinitionCorrespondence.lean",
                      "fc_theorems_in_order": fc_theorems,
                      "sealed_files": len(manifest)}, indent=2))

if __name__ == "__main__":
    main()

