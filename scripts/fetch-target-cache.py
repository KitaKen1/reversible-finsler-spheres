#!/usr/bin/env python3
"""Fetch pinned dependency caches only for imports of the requested proof targets.

Compiled project/Tau Ceti/Lean Pool modules are still built from source. Compressed
downloads live in one automatically cleaned temporary directory.
"""
from pathlib import Path
import argparse
import json
import os
import re
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
code_only = runpy.run_path(str(ROOT / "scripts/check-package.py"),
                          run_name="cache_import_helpers")["code_only"]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--project", type=Path, default=ROOT / "lean")
    ap.add_argument("--dependency-project", type=Path,
                    help="Read-only dependency sources for --list against a matching local build")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("targets", nargs="*", default=["FCExactChallenge", "FCExactSolution", "FCExactAudit"])
    args = ap.parse_args()
    project = args.project.resolve()
    dependencies = (args.dependency_project or project).resolve()
    if args.dependency_project and not args.list:
        ap.error("--dependency-project is only for read-only planning with --list")
    if not args.list:
        # Lake materializes the exact manifest pins before we inspect package sources.
        subprocess.run(["lake", "env", "lean", "--version"], cwd=project, check=True)
    manifest = json.loads((project / "lake-manifest.json").read_text())
    if args.dependency_project:
        for name in ["lake-manifest.json", "lean-toolchain"]:
            assert (project / name).read_bytes() == (dependencies / name).read_bytes(), name
    package_dir = dependencies / ".lake/packages"
    bases = [project] + [package_dir / p["name"].strip("«»") for p in manifest["packages"]]
    cache_io = package_dir / "mathlib/Cache/IO.lean"
    cache_predicate = code_only(cache_io.read_text()).split("def isPartOfMathlibCache", 1)[1]
    cache_predicate = cache_predicate.split("].contains mod.getRoot", 1)[0]
    cached_prefixes = set(re.findall(r"`([A-Za-z][A-Za-z0-9]*)", cache_predicate))
    assert "Mathlib" in cached_prefixes
    seen, roots, pending = set(), set(), list(args.targets)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        prefix = name.split(".", 1)[0]
        if prefix in {"Init", "Lean", "Std", "Lake"}:
            continue
        if prefix in cached_prefixes:
            roots.add(name)
            continue
        filename = name.replace(".", "/") + ".lean"
        source = next((base / filename for base in bases if (base / filename).is_file()), None)
        if source is None:
            raise SystemExit("Missing import source: " + name)
        for line in code_only(source.read_text()).splitlines():
            match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", line)
            if not match:
                continue
            for imported in match.group(1).split():
                if imported == "all":
                    continue
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", imported):
                    raise SystemExit("Unsupported module syntax: " + imported)
                pending.append(imported)
    assert roots and "Mathlib" not in roots, "Refusing an unbounded whole-Mathlib cache request"
    report = {"targets": args.targets, "visited_modules": len(seen),
              "cache_roots_count": len(roots), "cache_roots": sorted(roots),
              "compressed_downloads": "temporary; removed on success or failure"}
    if args.list:
        print(json.dumps(report, indent=2))
        return
    results = ROOT / "runtime-results"
    results.mkdir(exist_ok=True)
    (results / "fc-target-cache-plan.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Fetching", len(roots), "dependency cache roots for", len(seen), "visited modules", flush=True)
    with tempfile.TemporaryDirectory(prefix="fc-dependency-cache-") as temporary:
        env = dict(os.environ, MATHLIB_CACHE_DIR=temporary)
        subprocess.run(["lake", "exe", "cache", "get"] + sorted(roots),
                       cwd=project, env=env, check=True)


if __name__ == "__main__":
    main()
