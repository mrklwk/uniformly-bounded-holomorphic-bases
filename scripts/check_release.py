#!/usr/bin/env python3
"""Offline release invariants; not a full schema validator or Palomar acceptance."""
from pathlib import Path
import hashlib, json, re
root = Path(__file__).resolve().parents[1]
def read(name): return (root / name).read_text()
def unique(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result, f"Duplicate metadata key: {key}"
        result[key] = value
    return result
meta = json.loads(read('formalization.yaml'), object_pairs_hook=unique)
assert len(read('formalization.yaml').encode()) <= 256 * 1024
assert meta['version'] == 'v0.4'
p = meta['project']
assert p['name'] == read('README.md').splitlines()[0][2:]
assert 0 < len(p['name']) <= 300 and 0 < len(p['description']) <= 10000
assert p['authors'] == p['responsible_maintainers'] == ['Mark Lewko']
# Palomar's pinned Licensee reports the legacy AGPL-3.0 label for LICENSE.
# The explicit original-contribution grant remains AGPL-3.0-only.
assert p['license'] == 'AGPL-3.0'
assert p['license_scope'].startswith('Original contributions: AGPL-3.0-only.')
assert hashlib.sha256((root/'NOTICE').read_bytes()).hexdigest() == '591703f3827722d85142c1975f07c2f47956c57a216f570a5c356f6a956dbd78'
# Exact approved AGPL-3.0 text: reject Apache/template or modified license text.
assert hashlib.sha256((root/'LICENSE').read_bytes()).hexdigest() == 'd8a6cc31abc16b6748c7a21f21611f5a1ec33f67d22ca23d7da1c19b95496bee'
assert meta['classification']['arxiv'] == ['math.CV', 'math.FA']
assert meta['automation']['methods'] and meta['review']['status']
assert meta['sources'] and all(s['title'] and s['authors'] and s['relationship'] for s in meta['sources'])
assert 'TEMPLATE:' not in read('formalization.yaml')
assert 'd>=2' in meta['status']['scope']
assert 'pending' in meta['status']['dimension_one']
assert 'unverified' in meta['sources'][0]['note']
assert read('lean-toolchain').strip() == 'leanprover/lean4:v4.35.0-rc2'
manifest = json.loads(read('lake-manifest.json'))
pins = {x['name']: x['rev'] for x in manifest['packages']}
assert pins['mathlib'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
for dep in manifest['packages']:
    assert re.fullmatch('[0-9a-f]{40}', dep['rev'])
    assert re.fullmatch(r'https://github\.com/[^/?#@]+/[^/?#@]+', dep['url'])
for entry in json.loads(read('third_party/licenses/inventory.json')):
    assert pins[entry['package']] == entry['revision']
    assert hashlib.sha256((root/entry['license_file']).read_bytes()).hexdigest() == entry['license_sha256']
w = json.loads(read('.github/workflows/palomar-preflight.yml'))
assert set(w['on']) == {'workflow_dispatch'}
assert w['permissions'] == {'contents': 'read'}
v = w['jobs']['verify']
pin = 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'
assert v['uses'] == 'PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@' + pin
assert v['with']['pipeline_commit'] == pin
assert v['with']['mode'] == 'full'
assert v['with']['execution_profile'] == 'palomar-standard-v1'
assert v['with']['commit'] == '${{ github.sha }}'
options = json.loads(v['with']['options'])
assert options['comparator_config_path'] == 'comparator.json'
assert options['formalization_metadata_path'] == 'formalization.yaml'
assert not (root/'formalization.yaml.draft').exists()
print('PASS: release metadata, exact AGPL license, dependency/license pins, workflow pins and manual trigger')
