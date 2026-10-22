#!/usr/bin/env python3
"""Explicitly seal the current publication files (does not rewrite proof-source pins)."""
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

root = Path(__file__).resolve().parents[1]
excluded = {".local-check", "runtime-results", ".git", ".lake", "__pycache__"}
files = {}
for p in sorted(root.rglob("*")):
    relative = p.relative_to(root)
    if any(part in excluded for part in relative.parts):
        continue
    if p.is_symlink():
        raise SystemExit("Refusing publication symlink: " + str(relative))
    if not p.is_file() or p.name in {"PUBLICATION-MANIFEST.json", ".DS_Store"}:
        continue
    files[str(relative)] = hashlib.sha256(p.read_bytes()).hexdigest()
manifest = {"format_version": 1, "source_snapshot": "v188 plus common_eq proof refactor and public FC module wrappers",
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "publication_state": "candidate; verification outcomes recorded separately in verification/STATUS.md",
            "files_sha256": files}
(root / "PUBLICATION-MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
print("Sealed", len(files), "files; now run python3 scripts/check-package.py")

