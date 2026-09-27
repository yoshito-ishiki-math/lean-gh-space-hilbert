from pathlib import Path
import json, hashlib, re
p=Path(__file__).resolve().parent
assert (p/'Challenge.lean').read_text().count('sorry') == 1
assert not re.search(r'\b(sorry|admit)\b',(p/'Solution.lean').read_text())
assert re.findall(r'^import (.+)$',(p/'Challenge.lean').read_text(),re.M)==['Mathlib']
assert 'import Challenge' not in (p/'Solution.lean').read_text()
assert len((p/'Challenge.lean').read_bytes())<100*1024
assert len((p/'Challenge.lean').read_text().splitlines())<1000
j=json.loads((p/'comparator.json').read_text())
assert j['theorem_names']==['PalomarPaperN.main']
assert set(j['permitted_axioms'])=={'propext','Quot.sound','Classical.choice'}
for dep in json.loads((p/'lake-manifest.json').read_text())['packages']:
 assert re.fullmatch('[0-9a-f]{40}',dep['rev'])
 assert dep['url'].startswith('https://github.com/')
bad={'.olean','.ilean','.a','.bc','.dll','.dylib','.o','.obj','.so','.trace'}
files=[f for f in p.rglob('*') if f.is_file() and '.lake' not in f.relative_to(p).parts and '.git' not in f.relative_to(p).parts]
assert not any(f.is_symlink() or f.suffix in bad for f in files)
assert sum(f.stat().st_size for f in files)<500*1024*1024
hashes={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files if f.name!='package-hashes.json'}
(p/'submission-checks/package-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(f'Local structural checks passed: {len(files)} files. Comparator/NanoDa not checked.')
