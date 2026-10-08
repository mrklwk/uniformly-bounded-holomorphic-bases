#!/usr/bin/env python3
"""Read-only check for an already installed Linux target toolchain; never installs or runs it."""
import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--prefix', required=True, type=Path)
args = parser.parse_args()
prefix = args.prefix.resolve()
required = ['lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron']
missing = [name for name in required if not os.access(prefix / 'bin' / name, os.X_OK)]
issues = []
if platform.system() != 'Linux':
    issues.append('Official Linux sandbox route unavailable on this host')
if not shutil.which('bwrap'):
    issues.append('bwrap unavailable')
version = None
if 'lean' not in missing:
    version = subprocess.check_output([str(prefix / 'bin' / 'lean'), '--version'], text=True).strip()
    if 'version 4.35.0-rc2' not in version:
        issues.append('Installed compiler does not match prepared v4.35.0-rc2 target')
if missing:
    issues.append('Missing required installed binaries: ' + ', '.join(missing))
print(json.dumps({'installed_version': version, 'issues': issues,
                  'comparator_run': False, 'nanoda_run': False,
                  'note': 'Passing preflight is not proof validation; provisioned exact dependencies are also required.'}, indent=2))
raise SystemExit(1 if issues else 0)
