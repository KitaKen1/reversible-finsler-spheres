#!/usr/bin/env python3
"""Compile standalone FC statements and check correspondence with the proof projects.

Only small temporary oleans are written; no project or dependency tree is copied.
The four FC placeholders are not proofs. The separate implication module is
compiled and audited without importing those placeholders.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-build", type=Path, default=ROOT / "lean")
    parser.add_argument("--fc-source", type=Path, required=True,
                        help="Read-only upstream Formal Conjectures checkout")
    parser.add_argument("--record", action="store_true",
                        help="Save this run's log and source-hashed receipt in verification/local")
    args = parser.parse_args()
    source = args.source_build.resolve()
    manifest = json.loads((ROOT / "verification/proof-source-manifest.json").read_text())
    for name, expected in manifest["files_sha256"].items():
        if sha(source / name) != expected:
            raise SystemExit("Source build differs from the proof snapshot: " + name)
    for name in ["lean-toolchain", "lake-manifest.json"]:
        if (source / name).read_bytes() != (ROOT / "lean" / name).read_bytes():
            raise SystemExit("Dependency configuration differs: " + name)
    inherited = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                        cwd=source, text=True).strip()
    inherited = os.pathsep.join(str((source / p).resolve()) if not Path(p).is_absolute() else p
                               for p in inherited.split(os.pathsep) if p)
    lean = subprocess.check_output(["lake", "env", "which", "lean"],
                                   cwd=source, text=True).strip()
    # FC compilation can see only Mathlib's pinned dependency closure, never the
    # project's build directory, Tau Ceti, Lean Pool, or the proof-side adapters.
    mathlib_manifest = json.loads((source / ".lake/packages/mathlib/lake-manifest.json").read_text())
    expected_names = {p["name"] for p in mathlib_manifest["packages"]} | {"mathlib"}
    standalone_paths = [Path(p) for p in inherited.split(os.pathsep)
                        if len(Path(p).parents) > 3 and
                        Path(p).parents[3].name in expected_names and
                        Path(p).parts[-4:] == (".lake", "build", "lib", "lean")]
    assert {p.parents[3].name for p in standalone_paths} == expected_names
    standalone = os.pathsep.join(str(p) for p in standalone_paths)
    jobs = [
        ("upstream-ams-attributes", "_upstream/FormalConjecturesUtil/Attributes/AMS.lean",
         "_upstream", "FormalConjecturesUtil/Attributes/AMS"),
        ("upstream-category-attributes", "_upstream/FormalConjecturesUtil/Attributes/Basic.lean",
         "_upstream", "FormalConjecturesUtil/Attributes/Basic"),
        ("four-fc-statements", "FClikelean/ReversibleFinslerSpheres.lean",
         "FClikelean", "ReversibleFinslerSpheres"),
        ("standalone-statement-and-metadata-readback", "verification/FCStatementReadback.lean",
         "verification", None),
        ("proof-target-definitions", "lean/FCTargetDefinitions.lean", "lean", "FCTargetDefinitions"),
        ("definition-correspondence-and-axioms", "verification/FCDefinitionCorrespondence.lean",
         "verification", None),
        ("higher-dimensional-solution", "lean/FCSolution.lean", "lean", "FCSolution"),
        ("proved-implications", "lean/FCImplications.lean", "lean", "FCImplications"),
        ("implications-readback-and-axioms", "verification/FCImplicationsReadback.lean",
         "verification", None)]
    def input_path(name):
        if name.startswith("_upstream/"):
            return args.fc_source.resolve() / name.removeprefix("_upstream/")
        return ROOT / name
    inputs = [job[1] for job in jobs] + ["scripts/check-fc-statements.py"]
    receipt = {"kind": "incremental-fc-statement-elaboration-and-readback",
               "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "lean_toolchain": (source / "lean-toolchain").read_text().strip(),
               "source_files_matched": len(manifest["files_sha256"]),
               "clean_build": False, "proof_validation": False,
               "proof_scope": "n >= 3 solution and implication theorems; n = 2 supplied by literature, outside Lean proof scope",
               "fc_import_check": "Mathematical body unchanged; standard FC import expanded to official attributes and used Mathlib modules for cross-version correspondence. Exact upstream import is checked separately by check-fc-upstream.py.",
               "expected_fc_placeholders": 4,
               "fc_isolated_from_proof_projects": True,
               "fc_dependency_packages": sorted(expected_names),
               "inputs_sha256": {name: sha(input_path(name)) for name in inputs}, "checks": []}
    output = []
    success = True
    with tempfile.TemporaryDirectory(prefix="finsler-fc-statements-") as folder:
        work = Path(folder)
        fc_work, proof_work = work / "fc", work / "proof"
        fc_work.mkdir()
        proof_work.mkdir()
        generated = work / "statements"
        generated.mkdir()
        statement = (ROOT / "FClikelean/ReversibleFinslerSpheres.lean").read_text()
        expanded = statement.replace("public import FormalConjecturesUtil\n",
            "public import FormalConjecturesUtil.Attributes.Basic\n"
            "public import Mathlib.Geometry.Manifold.Instances.Sphere\n"
            "public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv\n"
            "public import Mathlib.Analysis.InnerProductSpace.Calculus\n"
            "public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic\n")
        assert expanded != statement
        (generated / "ReversibleFinslerSpheres.lean").write_text(expanded)
        receipt["expanded_imports_sha256"] = sha(generated / "ReversibleFinslerSpheres.lean")
        for label, name, root, module in jobs:
            isolated = root in {"FClikelean", "_upstream"} or label == "standalone-statement-and-metadata-readback"
            destination_root = fc_work if isolated else proof_work
            search_path = (str(fc_work) + os.pathsep + standalone if isolated else
                           os.pathsep.join([str(proof_work), str(fc_work), inherited]))
            env = dict(os.environ, LEAN_PATH=search_path)
            root_path = args.fc_source.resolve() if root == "_upstream" else ROOT / root
            source_path = input_path(name)
            if label == "four-fc-statements":
                root_path, source_path = generated, generated / "ReversibleFinslerSpheres.lean"
            cmd = [lean, "-M4096", "-j2", "-DElab.async=false", "--root=" + str(root_path)]
            if module:
                target = destination_root / (module + ".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                cmd += ["-o", str(target)]
            cmd.append(str(source_path))
            print("START", label, flush=True)
            start = time.monotonic()
            try:
                result = subprocess.run(cmd, cwd=ROOT / "FClikelean" if isolated else source,
                                        env=env, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
                code, raw = result.returncode, result.stdout
                status = "pass" if code == 0 else "fail"
            except subprocess.TimeoutExpired as error:
                code, raw, status = None, error.stdout or b"", "timeout"
                if isinstance(raw, bytes):
                    raw = raw.decode("utf-8", errors="replace")
            seconds = round(time.monotonic() - start, 3)
            warnings = len(re.findall(r"declaration uses [`']sorry[`']", raw))
            expected_warnings = 4 if label == "four-fc-statements" else 0
            if status == "pass" and warnings != expected_warnings:
                status = "unexpected-placeholder-count"
            for prefix, replacement in sorted([(str(ROOT), "[publication]"),
                                                (str(source), "[source-build]"),
                                                (str(work), "[temporary-build]")],
                                               key=lambda pair: -len(pair[0])):
                raw = raw.replace(prefix, replacement)
            output.append(f"{label}: {status} ({seconds}s)\n{raw}")
            receipt["checks"].append({"check": label, "status": status, "exit_code": code,
                                      "isolated_mathlib_only": isolated,
                                      "seconds": seconds, "sorry_warnings": warnings})
            print(output[-1], flush=True)
            if status != "pass":
                success = False
                break
    receipt["status"] = "pass" if success else "fail"
    receipt["temporary_build_removed"] = True
    receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if args.record:
        destination = ROOT / "verification/local"
        destination.mkdir(exist_ok=True)
        log = destination / "fc-four-statements.log"
        log.write_text("\n".join(output))
        receipt["log"] = str(log.relative_to(ROOT))
        receipt["log_sha256"] = sha(log)
        (destination / "fc-four-statements-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if not success:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
