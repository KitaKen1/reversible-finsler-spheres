#!/usr/bin/env python3
"""Bounded local checks reusing an existing build, without modifying it.

This is an incremental source-matched check, not a clean build certificate.
The supplied build and Comparator tools must be trusted local installations.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TARGETS = ["ReversibleFinslerSphereFC.infinitely_many_prime_closed_geodesics",
           "ReversibleFinslerSphereFC.variational_form"]
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

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source-build", type=Path, required=True)
    ap.add_argument("--fc-source", type=Path, required=True)
    ap.add_argument("--comparator", type=Path)
    ap.add_argument("--exporter", type=Path)
    ap.add_argument("--replay-seconds", type=int, default=180)
    args = ap.parse_args()
    source = args.source_build.resolve()
    work = ROOT / ".local-check"
    work.mkdir(exist_ok=True)
    logs = ROOT / "verification" / "local"
    logs.mkdir(parents=True, exist_ok=True)
    receipt = {"kind": "incremental-source-matched-local-check", "sandbox": False,
               "clean_build": False, "external_kernel": False,
               "checks": [], "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    receipt_file = logs / "receipt.json"

    def save():
        receipt_file.write_text(json.dumps(receipt, indent=2) + "\n")

    manifest = json.loads((ROOT / "verification/proof-source-manifest.json").read_text())
    for name, expected in manifest["files_sha256"].items():
        for base in [source, ROOT / "lean", ROOT / "leanWithoutComparator"]:
            if sha(base / name) != expected:
                raise SystemExit("Source hash mismatch: " + name)
    for name in ["lean-toolchain", "lake-manifest.json"]:
        if (source / name).read_bytes() != (ROOT / "lean" / name).read_bytes():
            raise SystemExit("Dependency configuration differs: " + name)
    receipt["source_files_matched_per_variant"] = len(manifest["files_sha256"])
    receipt["lean_toolchain"] = (source / "lean-toolchain").read_text().strip()
    receipt["source_match_caveat"] = "Source hashes match; reused oleans are not a clean rebuild."
    save()
    inherited = lake_path(source)
    env = dict(os.environ)
    lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=source, text=True).strip()

    def run(label, cmd, cwd=source, limit=600, export=None, allowed_failure=False):
        log = logs / (label + ".log")
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
        # Only machine-specific path prefixes are redacted in public logs.
        raw = log.read_bytes()
        replacements = [(str(ROOT), "[publication]"), (str(source), "[source-build]")]
        if args.comparator:
            replacements.append((str(args.comparator.resolve()), "[comparator-checkout]"))
        if args.exporter:
            replacements.append((str(args.exporter.resolve().parents[3]), "[exporter-checkout]"))
        normalized = raw.decode("utf-8", errors="replace")
        for prefix, replacement in sorted(replacements, key=lambda pair: -len(pair[0])):
            normalized = normalized.replace(prefix, replacement)
        log.write_text(normalized)
        record = {"check": label, "status": status, "exit_code": code,
                  "seconds": round(time.monotonic() - start, 3),
                  "log": "verification/local/" + log.name,
                  "raw_log_sha256": hashlib.sha256(raw).hexdigest(),
                  "log_normalization": "machine-specific path prefixes only"}
        receipt["checks"].append(record)
        save()
        print(status.upper(), label, record["seconds"], flush=True)
        if status != "pass" and not allowed_failure:
            raise SystemExit("Check failed; see " + str(log))
        return status

    output = work / "lean"
    output.mkdir(exist_ok=True)
    env["LEAN_PATH"] = str(output) + os.pathsep + inherited
    for module in ["FCTargetDefinitions", "Challenge"]:
        run("lean-" + module, [lean, "-M4096", "-j2", "-DElab.async=false",
            "--root=" + str(ROOT / "lean"), "-o", str(output / (module + ".olean")),
            str(ROOT / "lean" / (module + ".lean"))])
    run("fc-statements-and-implications", ["python3", str(ROOT / "scripts/check-fc-statements.py"),
        "--source-build", str(source), "--fc-source", str(args.fc_source.resolve()), "--record"])
    for module in ["FCSolution", "FCImplications", "FCAudit", "SpecificationReadback"]:
        run("lean-" + module, [lean, "-M4096", "-j2", "-DElab.async=false",
            "--root=" + str(ROOT / "lean"), "-o", str(output / (module + ".olean")),
            str(ROOT / "lean" / (module + ".lean"))])
    second = work / "without-comparator"
    second.mkdir(exist_ok=True)
    env["LEAN_PATH"] = str(second) + os.pathsep + inherited
    for module in ["FCTargetDefinitions", "FCSolution", "FCImplications", "FCAudit", "SpecificationReadback"]:
        run("without-" + module, [lean, "-M4096", "-j2", "-DElab.async=false",
            "--root=" + str(ROOT / "leanWithoutComparator"), "-o",
            str(second / (module + ".olean")),
            str(ROOT / "leanWithoutComparator" / (module + ".lean"))])

    if args.comparator and args.exporter:
        comparator = args.comparator.resolve()
        pins = json.loads((ROOT / "lean/comparator/pins.json").read_text())
        for folder, key in [(comparator, "comparator_commit"),
                            (args.exporter.resolve().parents[3], "lean4export_commit")]:
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=folder, text=True).strip()
            dirty = subprocess.check_output(["git", "status", "--porcelain"], cwd=folder, text=True).strip()
            if revision != pins[key] or dirty:
                raise SystemExit("Tool checkout does not match clean pin: " + key)
            receipt[key] = revision
        env["LEAN_PATH"] = str(output) + os.pathsep + inherited
        for module in ["Challenge", "FCSolution"]:
            run("export-" + module, [str(args.exporter.resolve()), module, "--"] +
                TARGETS + PRIMITIVES, export=work / (module + ".export"))
        # Both checker and exporter have a Main module; select the checker first.
        env["LEAN_PATH"] = str(comparator / ".lake/build/lib/lean") + os.pathsep + lake_path(comparator)
        env["PUBLICATION_EXPORT_DIR"] = str(work)
        driver = ROOT / "lean/comparator/CompareExports.lean"
        run("comparator-structure-and-axioms", [lean, "-M4096", "-j2",
            "-DElab.async=false", str(driver)], cwd=comparator, limit=600)
        if args.replay_seconds > 0:
            env["PUBLICATION_REPLAY"] = "1"
            run("comparator-builtin-kernel-replay", [lean, "-M4096", "-j2",
                "-DElab.async=false", str(driver)], cwd=comparator,
                limit=args.replay_seconds, allowed_failure=True)
        # Export streams are reproducible intermediate products, not publication evidence.
        for module in ["Challenge", "FCSolution"]:
            (work / (module + ".export")).unlink(missing_ok=True)
    receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    save()

if __name__ == "__main__":
    try:
        main()
    finally:
        # Also remove large exports on a failed check or an interrupted local run.
        for module in ["Challenge", "FCSolution"]:
            (ROOT / ".local-check" / (module + ".export")).unlink(missing_ok=True)

