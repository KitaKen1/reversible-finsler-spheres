#!/usr/bin/env python3
"""Build the local import closure one module at a time (dependencies remain pinned)."""
from pathlib import Path
import argparse
import re
import subprocess

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--project", type=Path, default=Path("lean"))
ap.add_argument("--list", action="store_true", help="Print the build plan without executing it")
ap.add_argument("--warm-target", action="append", default=[],
                help="Validate a cached import closure with Lake before omitting its per-module invocations")
ap.add_argument("targets", nargs="*", default=["FCExactSolution", "FCExactAudit"])
args = ap.parse_args()
root = args.project.resolve()
seen, active, order, dependencies = set(), set(), [], {}
def visit(name):
    file = root / (name.replace(".", "/") + ".lean")
    if not file.exists() or name in seen:
        return
    if name in active:
        raise SystemExit("Import cycle: " + name)
    active.add(name)
    dependencies[name] = []
    for line in file.read_text().splitlines():
        match = re.match(r"^(?:public\s+|private\s+)?import\s+([A-Za-z0-9_.]+)\s*(?:--.*)?$", line)
        if match:
            dependencies[name].append(match.group(1))
            visit(match.group(1))
    active.remove(name)
    seen.add(name)
    order.append(name)
for target in args.targets:
    visit(target)
if not order:
    raise SystemExit("No project modules found")
if not args.list:
    for target in args.warm_target:
        if target not in seen:
            raise SystemExit("Warm target is outside the requested import closure: " + target)
        # Lake, rather than file existence or our own hash heuristic, validates
        # every transitive source/option/artifact trace. --no-build never starts
        # a parallel rebuild. A stale or absent cache falls back to serial work.
        print("Checking cached closure:", target, flush=True)
        checked = subprocess.run(["lake", "--no-build", "--log-level=error", "build",
                                  "+" + target + ":olean"], cwd=root,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if checked.returncode == 0:
            verified, pending = set(), [target]
            while pending:
                name = pending.pop()
                if name in seen and name not in verified:
                    verified.add(name)
                    pending.extend(dependencies[name])
            order = [name for name in order if name not in verified]
            print("Lake validated", len(verified), "cached project modules;",
                  len(order), "serial modules remain", flush=True)
        else:
            print("Cached closure is not current; using the full serial build", flush=True)
for i, name in enumerate(order, 1):
    print(f"[{i}/{len(order)}] {name}", flush=True)
    if not args.list:
        # Keep one progress line per module. Lake otherwise replays every
        # dependency's stored warnings on every invocation (over 550k log lines
        # in the first source build). Failed targets still print their errors.
        subprocess.run(["lake", "--log-level=error", "build", "+" + name + ":olean"],
                       cwd=root, check=True)

