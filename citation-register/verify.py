"""Validate the fixed citation register, not its mathematical conclusions.
Run from the repository root: uv run python formalizations/ghsp-topology/paperN/citation-register/verify.py
"""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
register = json.loads((HERE / 'REGISTER.json').read_text())
snapshot = json.loads((HERE / 'SNAPSHOT.json').read_text())
for name, expected in snapshot.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected, name
visited = set()
actual = []

def visit(path):
    if path in visited:
        return
    visited.add(path)
    text = re.sub(r'(?<!\\)%[^\n]*', '', path.read_text())
    for match in re.finditer(r'\\(?:input|include)\{([^}]+)\}', text):
        child = ROOT / 'paperN' / match[1]
        visit(child if child.suffix else child.with_suffix('.tex'))
    for match in re.finditer(r'\\(?:cite|parencite|textcite)(?:\[([^\]]*)\])?\{([^}]+)\}', text):
        actual.append((str(path.relative_to(ROOT)), text[:match.start()].count('\n') + 1,
                       match[1] or '', match[2]))

visit(ROOT / 'paperN/main.tex')
expected = [(r['file'], r['line'], r['locator'], r['keys']) for r in register['citations']]
assert actual == expected
assert len(visited) == register['counts']['tex_files']
keys = {k.strip() for r in actual for k in r[3].split(',')}
assert keys == {r['key'] for r in register['sources']}
bibkeys = set(re.findall(r'@\w+\s*\{\s*([^,]+),', (ROOT / 'paperN/bib/references.bib').read_text()))
assert keys <= bibkeys
for source in register['sources']:
    assert hashlib.sha256(Path(source['local_pdf']).read_bytes()).hexdigest() == source['sha256'], source['key']
assert len({r['id'] for r in register['citations']}) == len(actual)
print(json.dumps({'snapshot_files': len(snapshot), 'active_tex_files': len(visited),
                  'citation_occurrences': len(actual), 'source_keys': len(keys),
                  'pdf_hashes_passed': len(register['sources']), 'result': 'pass',
                  'boundary': 'Structural and byte-identity checks only; no mathematical proof certification.'}, indent=2))
