#!/usr/bin/env python3
"""Check the exact mathematical FC target with pinned upstream Comparator.

Reuses a source-matched proof build without modifying it. This is incremental,
not a clean-build certificate. Temporary oleans/exports are always removed.
The local Comparator API run does not claim an operating-system sandbox.
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
TARGET = "ReversibleFinslerSpheres.infinitely_many_prime_closed_geodesics"
PRIMITIVES = ["Quot", "propext", "Classical.choice", "Quot.sound",
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
    "Nat", "String", "String.mk", "Char", "optParam", "autoParam",
    "semiOutParam", "outParam"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lake_path(project):
    value = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                    cwd=project, text=True).strip()
    return os.pathsep.join(str((project / p).resolve()) if not Path(p).is_absolute()
                           else p for p in value.split(os.pathsep) if p)


def entry_setup(source, module, file, output, inherited):
    """Use Lake's import artifact format, including IR, for a bounded CI compile.

    The existing source build supplies dependency artifacts, not entry outputs.
    Old absolute paths in its setup files are relocated only to matching module
    artifacts on the checked build's Lean search path.
    """
    dependency = ("Finsler.Geometry.OrdinaryGeodesic"
                  if module in ["FCExactChallenge", "FCTargetDefinitions"]
                  else "Finsler.Residual.FillRel")
    relative = Path(dependency.replace(".", "/"))
    setup = json.loads((source / ".lake/build/ir" / relative.with_suffix(".setup.json")).read_text())
    imported = setup["importArts"]
    base = source / ".lake/build/lib/lean" / relative
    imported[dependency] = [[str(base.with_suffix(".olean")), str(base.with_suffix(".olean.server"))],
                            [str(base.with_suffix(".ir.sig")), str(base.with_suffix(".ir"))]]
    for name, artifact in imported.items():
        for group in artifact:
            for index, old in enumerate(group):
                if Path(old).is_file():
                    continue
                filename = Path(old).name
                suffix = filename[filename.index(".olean"):] if ".olean" in filename else filename[filename.index(".ir"):]
                for search in inherited.split(os.pathsep):
                    replacement = Path(search) / (name.replace(".", "/") + suffix)
                    if replacement.is_file():
                        group[index] = str(replacement)
                        break
                else:
                    raise RuntimeError("Missing dependency artifact: " + old)
    for olean in output.glob("*.olean"):
        base = olean.with_suffix("")
        imported[base.name] = [[str(olean), str(base.with_suffix(".olean.server"))],
                               [str(base.with_suffix(".ir.sig")), str(base.with_suffix(".ir"))]]
    is_module = bool(re.search(r"(?m)^module\s*$", file.read_text()))
    if not is_module:
        raise RuntimeError("CI entry points must retain the module system: " + str(file))
    result = {"name": module, "package": "reversibleFinsler", "isModule": True,
              "importArts": imported, "plugins": [], "dynlibs": [], "options": {}}
    prepared = output / (module + ".setup.json")
    prepared.write_text(json.dumps(result))
    return prepared


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source-build", type=Path, required=True)
    ap.add_argument("--comparator", type=Path, required=True)
    ap.add_argument("--exporter", type=Path, required=True)
    ap.add_argument("--replay-seconds", type=int, default=3600)
    args = ap.parse_args()
    if args.replay_seconds <= 0:
        ap.error("Kernel replay is required; --replay-seconds must be positive")
    source, comparator, exporter = (p.resolve() for p in
                                   [args.source_build, args.comparator, args.exporter])
    logs = ROOT / "verification/local"
    logs.mkdir(parents=True, exist_ok=True)
    work = ROOT / ".local-check"
    work.mkdir(exist_ok=True)
    receipt_file = logs / "fc-target-comparator-receipt.json"
    receipt = {"kind": "exact-fc-target-incremental-comparator-check",
               "target": TARGET, "sandbox": False, "clean_build": False,
               "external_kernel": False, "status": "running", "checks": [],
               "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}

    def save():
        receipt_file.write_text(json.dumps(receipt, indent=2) + "\n")

    env = dict(os.environ)
    env.pop("PUBLICATION_REPLAY", None)
    lean = subprocess.check_output(["lake", "env", "which", "lean"],
                                   cwd=source, text=True).strip()

    def run(label, cmd, cwd=source, limit=600, export=None):
        log = logs / ("fc-target-" + label + ".log")
        start = time.monotonic()
        print("START", label, flush=True)
        try:
            with log.open("w") as handle:
                if export is None:
                    result = subprocess.run(cmd, cwd=cwd, env=env, stdout=handle,
                                            stderr=subprocess.STDOUT, timeout=limit)
                else:
                    with export.open("w") as out:
                        result = subprocess.run(cmd, cwd=cwd, env=env, stdout=out,
                                                stderr=handle, timeout=limit)
            status = "pass" if result.returncode == 0 else "fail"
            code = result.returncode
        except subprocess.TimeoutExpired:
            status, code = "timeout", None
        raw = log.read_bytes()
        normalized = raw.decode("utf-8", errors="replace")
        for prefix, replacement in sorted([
                (str(ROOT), "[publication]"), (str(source), "[source-build]"),
                (str(comparator), "[comparator-checkout]"),
                (str(exporter.parents[3]), "[exporter-checkout]")],
                key=lambda pair: -len(pair[0])):
            normalized = normalized.replace(prefix, replacement)
        log.write_text(normalized)
        record = {"check": label, "status": status, "exit_code": code,
                  "seconds": round(time.monotonic() - start, 3),
                  "log": "verification/local/" + log.name,
                  "raw_log_sha256": hashlib.sha256(raw).hexdigest(),
                  "log_sha256": sha(log),
                  "log_normalization": "machine-specific path prefixes only"}
        receipt["checks"].append(record)
        save()
        print(status.upper(), label, record["seconds"], flush=True)
        if status != "pass":
            raise RuntimeError("Check failed; see " + str(log))

    save()
    try:
        run("generated-source-match", ["python3", str(ROOT / "scripts/generate-fc-target.py"),
                                        "--check"])
        manifest = json.loads((ROOT / "verification/proof-source-manifest.json").read_text())
        for name, expected in manifest["files_sha256"].items():
            for base in [source, ROOT / "lean", ROOT / "leanWithoutComparator"]:
                if sha(base / name) != expected:
                    raise RuntimeError("Source hash mismatch: " + name)
        for name in ["lean-toolchain", "lake-manifest.json"]:
            if (source / name).read_bytes() != (ROOT / "lean" / name).read_bytes():
                raise RuntimeError("Dependency configuration differs: " + name)
        receipt["source_files_matched_per_variant"] = len(manifest["files_sha256"])
        receipt["core_source_manifest_sha256"] = sha(ROOT / "verification/proof-source-manifest.json")
        receipt["lean_toolchain"] = (source / "lean-toolchain").read_text().strip()
        receipt["source_match_caveat"] = "Source hashes match; reused oleans are not a clean rebuild."
        receipt["fc_source_sha256"] = sha(ROOT / "FClikelean/ReversibleFinslerSpheres.lean")
        receipt["entry_sources_sha256"] = {name: sha(ROOT / name) for name in [
            "lean/FCExactChallenge.lean", "lean/FCExactSolution.lean", "lean/FCExactAudit.lean",
            "lean/FCTargetDefinitions.lean", "lean/FCSolution.lean", "lean/comparator-fc.json",
            "lean/comparator/CompareFCExports.lean", "scripts/generate-fc-target.py"]}
        pins = json.loads((ROOT / "lean/comparator/pins.json").read_text())
        for folder, key in [(comparator, "comparator_commit"),
                            (exporter.parents[3], "lean4export_commit")]:
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=folder, text=True).strip()
            dirty = subprocess.check_output(["git", "status", "--porcelain"], cwd=folder, text=True).strip()
            if revision != pins[key] or dirty:
                raise RuntimeError("Tool checkout does not match clean pin: " + key)
            receipt[key] = revision
        save()
        inherited = lake_path(source)
        receipt["entry_compilation"] = {
            "memory_limit_MiB": 4096, "threads": 2, "Elab.async": False,
            "outputs": ["olean", "ilean", "c"], "lake_import_artifacts": True,
            "host_platform_caveat": "macOS incremental dependencies; hosted Linux build is separate"}
        with tempfile.TemporaryDirectory(prefix="fc-target-", dir=work) as tmp:
            temp = Path(tmp)
            for variant in ["lean", "leanWithoutComparator"]:
                output = temp / variant
                output.mkdir()
                env["LEAN_PATH"] = str(output) + os.pathsep + inherited
                modules = (["FCExactChallenge"] if variant == "lean" else []) + [
                    "FCTargetDefinitions", "FCSolution", "FCExactSolution", "FCExactAudit"]
                for module in modules:
                    file = ROOT / variant / (module + ".lean")
                    setup = entry_setup(source, module, file, output, inherited)
                    run(variant + "-" + module, [lean, "-M4096", "-j2", "-DElab.async=false",
                        "--root=" + str(ROOT / variant), "-o", str(output / (module + ".olean")),
                        "-i", str(output / (module + ".ilean")), "-c", str(output / (module + ".c")),
                        "--setup", str(setup), str(file)])
            env["LEAN_PATH"] = str(temp / "lean") + os.pathsep + inherited
            for module in ["FCExactChallenge", "FCExactSolution"]:
                run("export-" + module, [str(exporter), module, "--", TARGET] + PRIMITIVES,
                    export=temp / (module + ".export"))
            env["LEAN_PATH"] = str(comparator / ".lake/build/lib/lean") + os.pathsep + lake_path(comparator)
            env["PUBLICATION_EXPORT_DIR"] = str(temp)
            driver = ROOT / "lean/comparator/CompareFCExports.lean"
            run("comparator-structure-and-axioms", [lean, "-M8192", "-j2",
                "-DElab.async=false", str(driver)], cwd=comparator, limit=1200)
            env["PUBLICATION_REPLAY"] = "1"
            run("comparator-builtin-kernel-replay", [lean, "-M8192", "-j2",
                "-DElab.async=false", str(driver)], cwd=comparator, limit=args.replay_seconds)
        receipt["status"] = "pass"
    except BaseException as error:
        receipt["status"] = "fail"
        receipt["error"] = str(error).replace(str(ROOT), "[publication]")
        raise
    finally:
        receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        receipt["temporary_products_removed"] = True
        save()


if __name__ == "__main__":
    main()
