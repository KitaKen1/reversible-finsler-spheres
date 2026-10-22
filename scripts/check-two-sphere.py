#!/usr/bin/env python3
"""Compile and audit the proved two-sphere criteria in both proof variants.

Reuses a source-matched build. It does not copy the project or dependencies.
Temporary compiled modules are deleted on success, failure or timeout.
The nonzero-local-class, length-production and point-cover hypotheses remain
explicit: this check does not certify the unconditional two-sphere assertion.
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
TAUCETI_INPUTS = {
    "TauCeti.AlgebraicTopology.Singular.Empty":
        "b61088cbd7264aa10ccda5c99f9550a6b1507be2aeba17cd3b94fb9c514d3f4c",
    "TauCeti.AlgebraicTopology.Singular.DiskSphere":
        "0c40a901d895866e2cd8bd5ccc16e28b5970b2d624b25a978ae7f65c5e673716",
    "TauCeti.Topology.Homotopy.HomotopyEquiv":
        "1e0916254310fdb08450d4321db7a32fd48666039c30d6478f2ee5b94d60376d",
    "TauCeti.Topology.LocallyConnected":
        "968d6d3651f9229d44ff6e62c30f3ad058f0dc1d974d6f553fea956dd896db23",
    "TauCeti.Topology.JordanCurve.Basic":
        "c03dc70beeea0286c67059f8116a736ccaede585da6ef559874371273638f21e",
    "TauCeti.Topology.Homotopy.PuncturedStarConvex":
        "ca1bc30ae061a200a204857b4360ed4e692a3adab930bb4cb05cb1d237c4cf53",
    "TauCeti.GroupTheory.Perm.Basic":
        "8bb6cf6ddf8f3d41b7b5dbaa4c29be3890427213694496f1561d0e16d1586b6e",
    "TauCeti.Topology.Homeomorph.Semiconj":
        "1191a942372859a103594abf21fbd9c0023f84f83f07a720c2bc628c5331a528",
    "TauCeti.Topology.Instances.AddCircle.Defs":
        "c403955e00ba1588a7eaa81bb88a5f35f50a70d5a1cbcf8f080435e7c1d3dfc2",
    "TauCeti.Topology.MappingTorus":
        "4594110f8a5b5634f0ea9dcdb4319ed848fbe455f9fa8cec55a18b0b60c59c11",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependency_overlay(cache, destination, relative=Path()):
    """Reuse cached siblings by symlink; rebuild only the pinned modules.

    Lean resolves the whole top-level namespace at its first search-path hit.
    An overlay is therefore needed even for a small incremental build.
    No output path for a rebuilt module points into the shared cache.
    """
    changed = [Path(*module.split(".")[1:]) for module in TAUCETI_INPUTS]
    destination.mkdir(parents=True, exist_ok=True)
    for entry in cache.iterdir():
        name, target = relative / entry.name, destination / entry.name
        if entry.is_dir() and any(name in module.parents for module in changed):
            dependency_overlay(entry, target, name)
        elif any(relative == module.parent and entry.name.split(".")[0] == module.name
                 for module in changed):
            continue
        else:
            target.symlink_to(entry, target_is_directory=entry.is_dir())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-build", type=Path, default=ROOT / "lean")
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    source = args.source_build.resolve()
    manifest_path = ROOT / "verification/proof-source-manifest.json"
    manifest = json.loads(manifest_path.read_text())["files_sha256"]
    for name, expected in manifest.items():
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
    tau = (source / ".lake/packages/TauCeti").resolve()
    for module, expected in TAUCETI_INPUTS.items():
        if sha(tau / (module.replace(".", "/") + ".lean")) != expected:
            raise SystemExit("Tau Ceti source differs from the pinned input: " + module)
    modules = ["HingstonArithmetic", "HingstonBlocks", "HingstonConnectors", "HingstonPause", "HingstonFilling", "SurfaceLocalHomology", "SurfacePolygonHomology", "SurfaceMorseData", "SurfaceSpectralDisk", "SurfacePhaseGeometry", "SurfaceIteration", "SurfaceIterationHomology", "SurfaceIterationEquivalence", "SurfaceChainIndex", "SurfaceZeroMeanIndex", "SurfaceOrbitModel", "FCTargetDefinitions", "SurfaceMinimax", "FCTwoSphere"]
    inputs = [f"{variant}/{module}.lean" for variant in ["lean", "leanWithoutComparator"]
              for module in modules] + ["verification/TwoSphereReadback.lean",
                "scripts/check-two-sphere.py", "verification/proof-source-manifest.json"]
    receipt = {
        "kind": "incremental-two-sphere-criteria-and-axiom-audit",
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "lean_toolchain": (source / "lean-toolchain").read_text().strip(),
        "source_files_matched": len(manifest), "clean_build": False,
        "full_two_sphere_assertion_proved": False,
        "proof_scope": "Finite-spectrum arithmetic, continuous embedded loop-block families with exact energy, uniform deficits and actual relative sublevel maps, continuous short-connector families, energy-decreasing diagonal pause removal, actual enlarged interval-base families and homology vanishing by an explicit slide, exact iterate centers, nonzero local critical classes from coordinate and energy data with excision, split injection from actual polygon to Sobolev loop critical homology, exact critical polygon models and actual local splitting charts of every closed geodesic, small maximal disks and embedded nonzero loop classes from local product normal forms, spectral disk construction from a reduced kernel maximum and exact nullity loss under phase restriction, actual sampled phase curves and nonlinear transverse charts, identification of the genuine transverse Hessian and its degenerate splitting, actual transverse iteration with kernel equivalence and reduced-maximum transport, maximal disks along a bounded-gap odd nullity progression, actual local energy retractions and injections on point-critical homology under index/nullity preservation, construction of a stable base iterate for zero mean index and actual homology injections along an odd monodromy progression, energy-decreasing local deformations onto the actual repeated polygons, point-critical iteration isomorphisms and triviality of the base-period rotation action under index/nullity preservation, cutting periodic chain variations with a fixed two-edge cost, bounded index forcing all iterate indices to vanish, zero mean implying zero index for every geodesic iterate, positive index implying eventual growth above every bound, and original-geodesic iteration isomorphisms with original-period rotation action without stabilizing the base, a concrete invariant local repetition projection descending through the period-rotation mapping torus and proving fibre injectivity along an original-geodesic zero-mean progression, critical-value extraction from nonzero repeated local classes, and conditional criteria; 288 public theorems per variant",
        "additional_dependency_sources_sha256": TAUCETI_INPUTS,
        "inputs_sha256": {name: sha(ROOT / name) for name in inputs}, "checks": []}
    output, success = [], True
    with tempfile.TemporaryDirectory(prefix="finsler-two-sphere-check-") as folder:
        for variant in ["lean", "leanWithoutComparator"]:
            work = Path(folder) / variant
            work.mkdir()
            dependency_overlay(tau / ".lake/build/lib/lean/TauCeti", work / "TauCeti")
            env = dict(os.environ, LEAN_PATH=str(work) + os.pathsep + inherited)
            jobs = [("dependency/" + module,
                     str(tau / (module.replace(".", "/") + ".lean")), str(tau), module)
                    for module in TAUCETI_INPUTS]
            jobs += [(module, f"{variant}/{module}.lean", variant, module) for module in modules]
            jobs.append(("readback-and-axioms", "verification/TwoSphereReadback.lean", "verification", None))
            for label, name, root, module in jobs:
                label = variant + "/" + label
                cmd = [lean, "-M4096", "-j2", "-DElab.async=false", "--root=" + str(ROOT / root)]
                if module:
                    destination = work / (module.replace(".", "/") + ".olean")
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    cmd += ["-o", str(destination)]
                cmd.append(str(ROOT / name))
                print("START", label, flush=True)
                start = time.monotonic()
                try:
                    result = subprocess.run(cmd, cwd=source, env=env, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
                    code, raw = result.returncode, result.stdout
                    status = "pass" if code == 0 else "fail"
                except subprocess.TimeoutExpired as error:
                    code, raw, status = None, error.stdout or b"", "timeout"
                    if isinstance(raw, bytes):
                        raw = raw.decode("utf-8", errors="replace")
                seconds = round(time.monotonic() - start, 3)
                holes = len(re.findall(r"declaration uses [`']sorry[`']", raw))
                if status == "pass" and holes:
                    status = "unexpected-proof-placeholder"
                for prefix, replacement in sorted([(str(ROOT), "[publication]"),
                        (str(source), "[source-build]"), (str(tau), "[pinned-tau-ceti]"),
                        (folder, "[temporary-build]")],
                        key=lambda pair: -len(pair[0])):
                    raw = raw.replace(prefix, replacement)
                output.append(f"{label}: {status} ({seconds}s)\n{raw}")
                receipt["checks"].append({"check": label, "status": status,
                    "exit_code": code, "seconds": seconds, "sorry_warnings": holes})
                print(output[-1], flush=True)
                if status != "pass":
                    success = False
                    break
            if not success:
                break
    receipt["status"] = "pass" if success else "fail"
    receipt["temporary_build_removed"] = True
    receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if args.record:
        destination = ROOT / "verification/local"
        destination.mkdir(exist_ok=True)
        log = destination / "two-sphere.log"
        log.write_text("\n".join(output))
        receipt["log"] = str(log.relative_to(ROOT))
        receipt["log_sha256"] = sha(log)
        (destination / "two-sphere-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if not success:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
