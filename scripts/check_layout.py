#!/usr/bin/env python3
"""Check source packaging and literal interface agreement, not Comparator equivalence."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
challenge = (root / 'Challenge.lean').read_text()
solution = (root / 'Solution.lean').read_text()
imports = lambda text: re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', text, re.M)
assert imports(challenge) == ['Mathlib'], 'Challenge must import Mathlib alone'
assert 'BourgainBasis.' not in challenge, 'Challenge refers to project definitions'
assert len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000
definitions = lambda text: text.split('noncomputable section', 1)[1].split('theorem bar_eq', 1)[0].split('/-- Manuscript Theorem', 1)[0].strip()
statement = lambda text: text.split('/-- Manuscript Theorem', 1)[1].split(' := by', 1)[0]
assert definitions(challenge) == definitions(solution), 'Definition source mismatch'
assert statement(challenge) == statement(solution), 'Theorem source mismatch'
assert len(re.findall(r'\bsorry\b', challenge)) == 1
assert challenge.rstrip().endswith('sorry\n\nend BourgainStatement')
sources = {'.'.join(p.relative_to(root).with_suffix('').parts): p
           for p in root.rglob('*.lean') if '.lake' not in p.parts}
for name, path in sources.items():
    text = path.read_text()
    assert not path.is_symlink(), path
    assert text.startswith('module\n'), path
    assert len(text.splitlines()) <= 10000, path
    if name != 'Challenge':
        assert not re.search(r'\b(sorry|sorryAx|admit|native_decide|implemented_by)\b', text), path
        assert not re.search(r'^\s*axiom\s', text, re.M), path
seen = set()
def visit(name):
    assert name != 'Challenge', 'Solution imports Challenge transitively'
    if name in seen or name not in sources:
        return
    seen.add(name)
    for dependency in imports(sources[name].read_text()):
        visit(dependency)
visit('Solution')
config = json.loads((root / 'comparator.json').read_text())
assert config == {
    'challenge_module': 'Challenge', 'solution_module': 'Solution',
    'theorem_names': ['BourgainStatement.manuscript_main'],
    'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
print(json.dumps({'source_files': len(sources), 'challenge_lines': len(challenge.splitlines()),
                  'challenge_bytes': len(challenge.encode()), 'mathlib_only_challenge': True,
                  'literal_definitions_and_statement_match': True,
                  'solution_imports_challenge': False, 'challenge_placeholders': 1,
                  'proof_placeholders': 0, 'official_comparator_run': False}, indent=2))
