#!/usr/bin/env bash
# Adapted from PalomarTemplate/scripts/verify-comparator.sh (reviewed 2026-10-07).
# Uses the pinned project toolchain; no unsandboxed fallback.
set -euo pipefail
cd "$(dirname "$0")/.."
for tool in bwrap lake lean python3; do command -v "$tool" >/dev/null; done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool"
done
config=$(mktemp "${TMPDIR:-/tmp}/bourgain-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PYCONFIG'
import json, pathlib, sys
source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text())
assert "external_kernels" not in config, "external_kernels is not a submitter field"
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config) + "\n")
PYCONFIG
lake exe cache get
lake comparator --config "$config"
