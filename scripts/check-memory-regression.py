#!/usr/bin/env python3
"""Recompile the memory regression and exact FC audits against matching local dependencies."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import runpy
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Finsler.Loop.NativeSequentialSuffixMiddle"
DEPENDENT = "Finsler.Loop.NativeSequentialTripleComparison"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source-build", type=Path, required=True)
    args = ap.parse_args()
    source = args.source_build.resolve()
    manifest_file = ROOT / "verification/proof-source-manifest.json"
    manifest = json.loads(manifest_file.read_text())["files_sha256"]
    for name, digest in manifest.items():
        for base in [source, ROOT / "lean", ROOT / "leanWithoutComparator"]:
            assert sha(base / name) == digest, str(base / name)
    for name in ["lean-toolchain", "lake-manifest.json"]:
        assert (source / name).read_bytes() == (ROOT / "lean" / name).read_bytes(), name
    helpers = runpy.run_path(str(ROOT / "scripts/check-fc-comparator.py"))
    inherited = helpers["lake_path"](source)
    lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=source, text=True).strip()
    logs = ROOT / "verification/local"
    receipt_file = logs / "memory-regression-receipt.json"
    receipt = {"kind": "incremental-memory-regression", "clean_build": False,
               "kernel_replay": "not run", "status": "running", "checks": [],
               "core_source_manifest_sha256": sha(manifest_file),
               "memory_limit_MiB": 4096, "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    def save():
        receipt_file.write_text(json.dumps(receipt, indent=2) + "\n")
    save()
    try:
        with tempfile.TemporaryDirectory(prefix="fc-memory-", dir=ROOT / ".local-check") as temporary:
            for variant in ["lean", "leanWithoutComparator"]:
                output = Path(temporary) / variant
                entries = output / "entries"
                entries.mkdir(parents=True)
                # Lean selects a namespace from its first matching search root.
                # Keep the partial Finsler overlay out of LEAN_PATH; the two
                # core compiles use explicit setup artifact maps instead.
                env = dict(os.environ, LEAN_PATH=str(entries) + os.pathsep + inherited)
                modules = [MODULE, DEPENDENT, "FCTargetDefinitions", "FCSolution", "FCExactSolution", "FCExactAudit"]
                for module in modules:
                    relative = Path(module.replace(".", "/"))
                    file = ROOT / variant / relative.with_suffix(".lean")
                    module_output = output / "core" if module in [MODULE, DEPENDENT] else entries
                    olean = module_output / relative.with_suffix(".olean")
                    olean.parent.mkdir(parents=True, exist_ok=True)
                    cmd = [lean, "-M4096", "-j2", "-DElab.async=false", "--root=" + str(ROOT / variant), "-o", str(olean)]
                    setup_file = source / ".lake/build/ir" / relative.with_suffix(".setup.json")
                    if module in [MODULE, DEPENDENT]:
                        setup = json.loads(setup_file.read_text())
                        for imported, artifacts in setup["importArts"].items():
                            for index, path in enumerate(artifacts[0]):
                                old = Path(path)
                                new = output / "core" / imported.replace(".", "/")
                                suffix = old.name[old.name.index(".olean"):]
                                replacement = new.with_name(new.name + suffix)
                                if replacement.is_file():
                                    artifacts[0][index] = str(replacement)
                        prepared = output / (module + ".setup.json")
                        prepared.write_text(json.dumps(setup))
                        cmd += ["--setup", str(prepared)]
                    cmd.append(str(file))
                    label = variant + "-" + module
                    log = logs / ("memory-" + label + ".log")
                    start = time.monotonic()
                    print("START", label, flush=True)
                    with log.open("w") as handle:
                        result = subprocess.run(cmd, cwd=source, env=env, stdout=handle,
                                                stderr=subprocess.STDOUT, timeout=180)
                    text = log.read_text().replace(str(ROOT), "[publication]").replace(str(source), "[source-build]")
                    log.write_text(text)
                    receipt["checks"].append({"module": module, "variant": variant,
                        "status": "pass" if result.returncode == 0 else "fail", "exit_code": result.returncode,
                        "source_sha256": sha(file), "seconds": round(time.monotonic() - start, 3),
                        "log": "verification/local/" + log.name, "log_sha256": sha(log)})
                    save()
                    print(receipt["checks"][-1]["status"].upper(), label, flush=True)
                    if result.returncode:
                        raise RuntimeError("Compilation failed: " + label)
        receipt["status"] = "pass"
    except BaseException as error:
        receipt["status"] = "fail"
        receipt["error"] = str(error)
        raise
    finally:
        receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        receipt["temporary_products_removed"] = True
        save()


if __name__ == "__main__":
    main()
